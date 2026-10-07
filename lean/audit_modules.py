"""Build and audit selected Kneser modules; never infer manuscript completion.

Declaration discovery supports ordinary named theorem/lemma commands, namespace and
section blocks, attributes, and protected declarations. Unsupported theorem syntax
fails closed instead of silently omitting a declaration. Lean remains the authority
for compilation and axiom dependencies.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
IDENT = r"[^\W\d][\w']*"
LEAN_NAME = rf"{IDENT}(?:\.{IDENT})*"


class AuditError(RuntimeError):
    """The requested audit could not establish its advertised evidence."""


def strip_comments_and_strings(text):
    """Mask nested Lean comments and strings while preserving line positions."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out[i:i + 2] = "  "
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
            else:
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif string:
            if text[i] == "\\":
                out[i] = " "
                i += 1
                if i < len(text):
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
            else:
                if text[i] == '"':
                    string = False
                if text[i] != "\n":
                    out[i] = " "
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out[i:i + 2] = "  "
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            if end == -1:
                end = len(text)
            out[i:end] = " " * (end - i)
            i = end
        elif text[i] == '"':
            string = True
            out[i] = " "
            i += 1
        else:
            i += 1
    if depth or string:
        raise AuditError("Unterminated Lean comment or string")
    return "".join(out)


def collect_declarations(source):
    """Discover supported theorem and lemma declarations with their actual namespace."""
    code = strip_comments_and_strings(source.read_text())
    forbidden = re.search(r"\b(sorry|admit|axiom|native_decide|unsafe)\b", code)
    if forbidden:
        raise AuditError(f"{source}: forbidden source token {forbidden.group()}")
    declarations = []
    blocks = []  # (written block name, namespace before entry)
    namespace = ""
    for line_number, line in enumerate(code.splitlines(), 1):
        line = line.strip()
        match = re.fullmatch(rf"namespace\s+({LEAN_NAME})", line)
        if match:
            name = match.group(1)
            blocks.append((name, namespace))
            namespace = name.removeprefix("_root_.") if name.startswith("_root_.") else (
                f"{namespace}.{name}" if namespace else name)
            continue
        match = re.fullmatch(rf"(?:noncomputable\s+)?section(?:\s+({LEAN_NAME}))?", line)
        if match:
            blocks.append((match.group(1), namespace))
            continue
        match = re.fullmatch(rf"end(?:\s+({LEAN_NAME}))?", line)
        if match:
            if not blocks:
                raise AuditError(f"{source}:{line_number}: unmatched end")
            block_name, namespace = blocks.pop()
            if match.group(1) and match.group(1) != block_name:
                raise AuditError(f"{source}:{line_number}: mismatched named end")
            continue
        theorem_tokens = re.findall(r"\b(theorem|lemma)\b", line)
        if not theorem_tokens:
            continue
        if len(theorem_tokens) != 1:
            raise AuditError(f"{source}:{line_number}: multiple theorem/lemma commands on one line")
        # Attributes on the same line and on preceding lines are both accepted.
        match = re.match(
            rf"(?:@\[[^\]]*\]\s*)*(?:protected\s+)?(?:theorem|lemma)\s+"
            rf"({LEAN_NAME})(?=\s|[:(\[{{]|$)", line)
        if not match:
            raise AuditError(f"{source}:{line_number}: unsupported theorem/lemma syntax")
        name = match.group(1)
        qualified = name.removeprefix("_root_.") if name.startswith("_root_.") else (
            f"{namespace}.{name}" if namespace else name)
        declarations.append(qualified)
    # Lean permits an anonymous section (including `noncomputable section`)
    # to remain open until EOF. Explicit namespace/named-section blocks
    # still fail closed if the scanner cannot account for their end.
    if any(block_name is not None for block_name, _ in blocks):
        raise AuditError(f"{source}: unclosed namespace or section")
    return declarations


def source_hashes(root, sources):
    return {str(source.relative_to(root)): hashlib.sha256(source.read_bytes()).hexdigest()
            for source in sources}


def dependency_revisions(root):
    """Require clean dependency checkouts at the manifest's exact Git commits."""
    manifest = json.loads((root / "lake-manifest.json").read_text())
    revisions = {}
    for package in manifest["packages"]:
        if package.get("type") != "git":
            raise AuditError(f"Unsupported dependency type: {package['name']}")
        checkout = root / manifest["packagesDir"] / package["name"]
        result = subprocess.run(["git", "-C", str(checkout), "rev-parse", "HEAD"],
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if result.returncode or result.stdout.strip() != package["rev"]:
            raise AuditError(f"Dependency {package['name']} is not at its pinned revision")
        dirty = subprocess.run(["git", "-C", str(checkout), "status", "--porcelain",
                                "--untracked-files=no"], text=True,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if dirty.returncode or dirty.stdout:
            raise AuditError(f"Dependency {package['name']} has modified tracked files")
        revisions[package["name"]] = result.stdout.strip()
    return revisions


def run_logged(command, root, log_path):
    result = subprocess.run(command, cwd=root, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    log_path.write_text(result.stdout)
    if result.returncode:
        raise AuditError(f"Command failed ({result.returncode}): {' '.join(command)}\n"
                         f"See {log_path}\n{result.stdout}")
    return result.stdout


def audit_modules(root, name, modules):
    if not re.fullmatch(r"[a-z][a-z0-9-]*", name):
        raise AuditError("Audit name must match [a-z][a-z0-9-]*")
    if not modules or any(not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", x) for x in modules):
        raise AuditError("Provide at least one valid module name")
    if len(set(modules)) != len(modules):
        raise AuditError("Duplicate module names")
    audit = root / "audit"
    audit.mkdir(exist_ok=True)
    record_path = audit / (name + "-result.json")
    # A failed rerun must not leave an earlier PASS looking like its result.
    record_path.unlink(missing_ok=True)
    sources = [root / "Kneser" / (module + ".lean") for module in modules]
    all_source_modules_selected = sorted(modules) == sorted(
        source.stem for source in (root / "Kneser").glob("*.lean"))
    before = source_hashes(root, sources)
    configuration = [root / name for name in
                     ["lean-toolchain", "lakefile.toml", "lake-manifest.json",
                      "Kneser.lean", "check.py", "audit_modules.py"]]
    configuration_before = source_hashes(root, configuration)
    dependencies_before = dependency_revisions(root)
    declarations = [decl for source in sources for decl in collect_declarations(source)]
    if not declarations or len(set(declarations)) != len(declarations):
        raise AuditError("Expected a nonempty set of unique named declarations")

    build_command = ["lake", "build", *("Kneser." + module for module in modules)]
    run_logged(build_command, root, audit / (name + "-build.log"))
    if source_hashes(root, sources) != before:
        raise AuditError("Selected sources changed during the build; rerun the audit")
    lean_version = run_logged(["lake", "env", "lean", "--version"], root,
                              audit / (name + "-lean-version.log")).strip()
    file = audit / (name + "-axioms.lean")
    file.write_text("".join(f"import Kneser.{module}\n" for module in modules) +
                    "".join(f"#print axioms {decl}\n" for decl in declarations))
    output = run_logged(["lake", "env", "lean", str(file.relative_to(root))], root,
                        audit / (name + "-axioms.log"))
    # Lean identifiers may themselves contain apostrophes (e.g. bound').
    entries = re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]", output, re.M)
    empty = re.findall(r"^'(.+)' does not depend on any axioms", output, re.M)
    checked = [decl for decl, _ in entries] + empty
    if len(checked) != len(declarations) or set(checked) != set(declarations):
        raise AuditError("Lean axiom output did not account for every selected declaration exactly once")
    for decl, axioms in entries:
        used = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
        if not used <= ALLOWED_AXIOMS:
            raise AuditError(f"{decl}: disallowed axioms {sorted(used - ALLOWED_AXIOMS)}")
    if source_hashes(root, sources) != before:
        raise AuditError("Selected sources changed during the axiom audit; rerun the audit")
    if source_hashes(root, configuration) != configuration_before:
        raise AuditError("Build configuration, entry point or audit scripts changed during the audit")
    if dependency_revisions(root) != dependencies_before:
        raise AuditError("Dependency revisions changed during the audit")
    if all_source_modules_selected and sorted(modules) != sorted(
            source.stem for source in (root / "Kneser").glob("*.lean")):
        raise AuditError("Project source inventory changed during the audit")
    record = {
        "modules": modules, "checked_theorems": len(declarations), "declarations": declarations,
        "no_sorryAx": True, "no_custom_axioms": True,
        "allowed_foundational_axioms": sorted(ALLOWED_AXIOMS),
        "full_kneser_identity_formalized": False,
        "full_paper_first_order_formalized": False,
        "actual_attracting_prepared_series_first_order_formalized":
            "Kneser.PreparedActualFirstOrder.exists_actual_attracting_first_order" in declarations,
        "actual_exponential_preparation_constructed":
            "Kneser.ExponentialPreparedQuadratic.exists_actual_prepared_quadratic" in declarations,
        "actual_multiplier_parameter_derivative_formalized":
            "Kneser.ExponentialMultiplierParameter.exists_analytic_multiplier_parameter" in declarations,
        "actual_multiplier_parameter_second_order_formalized":
            "Kneser.ExponentialMultiplierSecondOrder.multiplier_second_order" in declarations,
        "actual_attracting_compact_uniform_explicit_coefficient_formalized":
            "Kneser.UniformActualAttracting.exists_actual_attracting_uniform_explicit_first_order"
            in declarations,
        "actual_repelling_compact_uniform_first_order_formalized":
            "Kneser.UniformRepellingFirstOrder.exists_actual_compact_repelling_first_order"
            in declarations,
        "actual_attracting_local_abel_equation_formalized":
            "Kneser.PreparedLocalAbel.exists_actual_local_prepared_abel" in declarations,
        "actual_attracting_common_holomorphic_abel_first_order_witnesses_formalized":
            "Kneser.ActualAttractingCoordinate.exists_actual_holomorphic_abel_first_order_coordinate"
            in declarations,
        "actual_repelling_explicit_compact_coefficient_formalized":
            "Kneser.ReflectedOrbitChainCoefficient.exists_actual_compact_repelling_explicit_coefficient"
            in declarations,
        "actual_repelling_local_abel_equation_formalized":
            "Kneser.ReflectedLocalAbel.exists_actual_local_inverse_prepared_abel" in declarations,
        "actual_repelling_common_holomorphic_abel_first_order_witnesses_formalized":
            "Kneser.ActualRepellingCoordinate.exists_actual_holomorphic_abel_repelling_first_order"
            in declarations,
        "actual_attracting_prepared_parabolic_abel_and_orbit_limit_formalized":
            "Kneser.PreparedParabolicAbel.exists_actual_prepared_parabolic_abel" in declarations,
        "actual_attracting_coefficient_spatial_holomorphy_formalized":
            "Kneser.PreparedCoefficientSpatialHolomorphy.exists_holomorphic_actualPreparedCoefficient"
            in declarations,
        "actual_repelling_coefficient_spatial_holomorphy_formalized":
            "Kneser.ReflectedCoefficientSpatialHolomorphy.exists_holomorphic_actualInversePreparedCoefficient"
            in declarations,
        "actual_attracting_canonical_coordinate_at_zero_formalized":
            "Kneser.PreparedCanonicalAtZero.exists_actual_prepared_canonical_at_zero"
            in declarations,
        "actual_repelling_canonical_coordinate_at_zero_formalized":
            "Kneser.ReflectedCanonicalAtZero.exists_actual_reflected_canonical_at_zero"
            in declarations,
        "actual_bilateral_explicit_coefficients_share_preparation_witnesses":
            "Kneser.BilateralFirstOrder.exists_actual_bilateral_explicit_first_order"
            in declarations,
        "actual_canonical_spatial_jacobians_constructed":
            "Kneser.ParabolicCoordinateJacobian.exists_bilateral_canonicalJacobian"
            in declarations,
        "actual_compact_uniform_bilateral_gate_constructed":
            "Kneser.ActualBilateralGate.exists_actual_bilateral_gate" in declarations,
        "actual_whole_canonical_image_gate_constructed":
            "Kneser.FullCanonicalImageGate.exists_whole_canonical_image_gate" in declarations,
        "actual_real_normalization_anchor_expansion_constructed":
            "Kneser.ActualNormalizationAnchorExpansion.exists_anchor_expansion_of_deep"
            in declarations,
        "actual_quantitative_moving_transition_constructed":
            "Kneser.ActualQuantitativeGateTransition.exists_actual_deep_abel_transition_data"
            in declarations,
        "actual_all_integer_fourier_first_order_expansion_constructed":
            "Kneser.ActualFourierExpansion.exists_actual_fourier_expansion" in declarations,
        "actual_transition_physical_chain_formula_formalized":
            "Kneser.ActualFourierExpansion.correction_eq_physical_formula" in declarations,
        "actual_periodic_fourier_expansion_and_absolute_orbit_formulas_share_witnesses":
            "Kneser.ActualFourierExpansion.exists_actual_periodic_fourier_expansion"
            in declarations,
        "actual_transition_translation_and_periodic_correction_formalized":
            "Kneser.ActualTransitionPeriodicity.correction_periodic" in declarations,
        "actual_exponential_lambda_factor_flatness_formalized":
            "Kneser.ActualLambdaFlatness.exists_actual_flat_lambda" in declarations,
        "actual_arbitrary_order_preparation_constructed":
            "Kneser.ExponentialPreparedHigher.exists_actual_prepared_order" in declarations,
        "actual_normalized_preparation_degree_compatibility_formalized":
            "Kneser.PreparedDegreeCompatibility.exists_actual_normalized_compatibility"
            in declarations,
        "actual_local_attracting_compact_uniform_all_orders_formalized":
            "Kneser.UniformActualHigherCoordinate.exists_actual_normalized_compact_all_orders"
            in declarations,
        "actual_local_all_orders_zero_and_coefficient_consistency_formalized":
            "Kneser.SharedPreparedConsistency.exists_actual_consistent_compact_all_orders"
            in declarations,
        "actual_bilateral_common_all_orders_baseline_constructed":
            "Kneser.ActualBilateralHigherPreparation.exists_actual_bilateral_common_all_orders"
            in declarations,
        "actual_bilateral_fixed_gate_all_orders_constructed":
            "Kneser.HigherGateTransport.exists_actual_bilateral_fixed_gate_all_orders"
            in declarations,
        "actual_normalized_positive_koenigs_constructed":
            "Kneser.PositiveLocalKoenigs.exists_actual_positive_koenigs" in declarations,
        "actual_prepared_positive_koenigs_identification_formalized":
            "Kneser.ActualKoenigsIdentification.exists_actual_prepared_koenigs_identification"
            in declarations,
        "actual_global_parabolic_coordinates_depth_independent":
            "Kneser.CanonicalDepthIndependence.globalAttracting_equal" in declarations and
            "Kneser.CanonicalDepthIndependence.globalRepelling_equal" in declarations,
        "actual_integral_fourier_reconstruction_formalized":
            "Kneser.ActualStripFourierRepresentation.exists_actual_canonical_fourier_representation"
            in declarations,
        "complex_center_gauge_invariance_formalized":
            "Kneser.FourierCenterShift.horn_gauge_invariant" in declarations,
        "parameter_dependent_gauge_logarithm_transfer_formalized":
            "Kneser.HornGaugeExpansion.gauge_logarithm_of_strip" in declarations,
        "weighted_fourier_nonlinear_sewing_constructed":
            "Kneser.FourierSewing.exists_nonlinear_sewing" in declarations,
        "weighted_fourier_normalizing_shift_constructed":
            "Kneser.FourierSewing.exists_normalizing_shift" in declarations,
        "weighted_fourier_same_witness_quantitative_sewing_constructed":
            "Kneser.FourierSewing.exists_quantitative_sewing" in declarations,
        "actual_band_height_and_lambda_scale_identified":
            "Kneser.ActualSewingScale.actual_band_exponential_scale" in declarations,
        "actual_parabolic_upper_infinity_model_bounds_formalized":
            "Kneser.CanonicalHighImaginaryAsymptotics.exists_upper_normalized_difference_bound"
            in declarations,
        "actual_common_inverse_coherent_all_order_horn_parameter_constructed":
            "Kneser.ActualAllOrderHornParameter.exists_actual_coherent_horn_parameter_expansion"
            in declarations,
        "actual_coherent_first_coefficient_equals_absolute_physical_orbit_formula":
            "Kneser.ActualRealNormalizedFirstCoefficient.exists_actual_physical_coherent_horn_expansion"
            in declarations,
        "actual_all_order_gate_identified_with_global_upper_horn_baseline":
            "Kneser.ActualAllOrderUpperHornBaseline.exists_actual_all_order_upper_horn_baseline"
            in declarations,
        "actual_global_upper_horn_integral_coefficient_identity_formalized":
            "Kneser.ActualUpperHornCoefficientIdentification.actual_baseline_nonzero_coefficient"
            in declarations,
        "actual_growing_lens_holomorphy_inverses_and_periodicity_constructed":
            "Kneser.ActualHolomorphicGrowingLens.exists_actual_lens_control" in declarations and
            "Kneser.ActualGrowingCoordinateInverse.exists_actual_bilateral_growing_inverses"
            in declarations,
        "actual_normalized_global_all_mode_fourier_decay_and_reconstruction":
            "Kneser.NormalizedGrowingFourier.exists_actual_normalized_growing_fourier"
            in declarations,
        "actual_same_all_order_global_horn_and_positive_koenigs_family_constructed":
            "Kneser.ActualGlobalHornFamily.exists_actual_global_horn_family" in declarations,
        "actual_same_horn_family_and_integral_fourier_sewing_identified":
            "Kneser.ActualGlobalSewingIdentification.exists_actual_global_sewn_horn_family"
            in declarations,
        "actual_integral_sewn_coefficient_lambda_comparison_constructed":
            "Kneser.ActualNormalizedSewing.exists_actual_integral_lambda_comparison"
            in declarations,
        "actual_scale_flatness_uniform_over_every_ordered_root_pair":
            "Kneser.ActualOrderedLambdaFlatness.actual_ordered_lambda_flat" in declarations,
        "same_all_order_coefficients_transfer_across_flat_sewing_error":
            "Kneser.FlatSewingLogTransfer.all_orders_log_of_flat_comparison" in declarations,
        "actual_constructed_sewing_all_orders_and_explicit_first_coefficient":
            "Kneser.ActualSewnAllOrders.exists_actual_sewn_all_orders" in declarations and
            "Kneser.MainResult.exists_actual_sewn_result" in declarations,
        "actual_selected_fibers_have_same_geometric_time_atlas":
            "Kneser.ActualSewingTimeAtlas.exists_actual_all_orders_time_atlas" in declarations,
        "actual_sewn_normalized_mode_ratios_have_coherent_all_order_expansions":
            "Kneser.ActualSewnModeRatios.actual_sewn_mode_ratio_all_orders" in declarations,
        "true_finite_iterates_construct_entire_poincare_extension":
            "Kneser.PoincareEntireExtension.exists_entire_extension" in declarations,
        "actual_unit_basin_koenigs_inverse_domain_period_abel_and_anchor_constructed":
            "Kneser.ActualRegularKoenigsInverse.actual_anchor_domain_and_value" in declarations and
            "Kneser.ActualRegularKoenigsInverse.actual_regular_transition_global" in declarations,
        "actual_regular_inverse_domain_contains_complete_right_half_plane":
            "Kneser.ActualRegularTimeHalfPlane.exists_actual_regular_right_halfPlane" in declarations,
        "actual_same_fiber_physical_function_normalization_abel_and_exact_log_germ":
            "Kneser.ActualFiberKoenigsUniformization.all_orders_data_physical_uniformization"
            in declarations,
        "actual_principal_koenigs_abel_integral_equals_sewn_time_integral":
            "Kneser.ActualRegularTimeLift.exists_actual_physical_lift_integral" in declarations,
        "actual_entire_repelling_coordinate_identified_with_same_growing_inverse":
            "Kneser.ActualEntireRepellingCoordinate.exists_actual_entire_repelling_of_control"
            in declarations,
        "actual_constructed_physical_sewing_first_order_closed":
            "Kneser.ActualPhysicalSewnCoefficients.exists_actual_physical_sewn_coefficients"
            in declarations and
            "Kneser.PhysicalMainResult.exists_actual_physical_first_order_result" in declarations,
        "actual_original_base_tetration_and_same_all_mode_integrals":
            "Kneser.ActualBaseTetration.base_family_of_physical_coefficients"
            in declarations,
        "actual_original_variable_first_order_and_coherent_all_orders_closed":
            "Kneser.OriginalMainResult.exists_actual_original_first_order_result"
            in declarations,
        "actual_complete_two_patch_physical_sewing_constructed":
            "Kneser.ActualGluedPhysicalSewing.glued_family_of_physical_coefficients"
            in declarations,
        "actual_two_patch_original_function_and_true_integral_all_orders_closed":
            "Kneser.GluedOriginalResult.exists_actual_glued_original_result"
            in declarations,
        "readable_interface_bundles_same_glued_family":
            "Kneser.Interface.exists_sewnTetrationFamily" in declarations and
            "Kneser.Interface.exists_sewn_tetration" in declarations and
            "Kneser.Interface.exists_sewn_tetration_all_orders" in declarations,
        "higher_order_semantic_scope":
            "One genuine real-anchor transition and one common centered repelling inverse "
            "carry all finite-order integer expansions, periodic continuation, actual "
            "Fourier/logarithm coefficients, the common multiplier parameter, and a "
            "coherent coefficient sequence with explicit absolute-orbit first coefficient. "
            "The same family is identified with the global upper-horn baseline and the "
            "positive Koenigs-normalized growing transition. Constructed Fourier sewing "
            "has genuine integral coefficients, the actual Lambda comparison, and the "
            "same coherent all-order expansion with an explicit physical first correction. "
            "A geometric time atlas uses the exact same selected Fourier corrections. "
            "The genuine physical sewing has its true normalization and Abel equation, "
            "and principal Koenigs lift integrals on a proved period line equal those "
            "same coefficients. The actual attracting inverse domain and the entire "
            "repelling coordinate are constructed and identified on their common lens. "
            "The proved affine conjugacy transports that same family to the original "
            "base exp((1-s)/e), with K(0)=1, the actual exponential iteration equation "
            "on a proved open domain, and identical normalized Koenigs integrals. "
            "The same upper physical chart is glued to the entire repelling chart "
            "on the whole lower half-plane, with holomorphy and the iteration equation "
            "on their open union. The resulting two-patch original function has the "
            "same true period-line integrals and coherent all-order coefficients. This "
            "does not certify identity with independently defined classical Kneser functions.",
        "some_generic_theorems_accept_analytic_orbit_hypotheses": True,
        "remaining_paper_dependencies": [
            "Identification of the constructed sewing with independently defined classical Kneser uniformization; transfer of the sewn integral coefficients to those classical coefficients",
            "Full complex parameter continuation and the remaining global identity statements of the manuscript",
            "Nonvanishing and numerical certificates used for specific manuscript modes, including B1, are not certified by the general nonzero-mode theorem",
        ],
        "scope": "Only the listed named theorem/lemma declarations and selected source hashes; "
                 "not a full-project completion audit or a dependency-source snapshot.",
        "sources_sha256": before,
        "configuration_sha256": configuration_before,
        "dependency_git_revisions": dependencies_before,
        "dependency_tracked_files_clean": True,
        "lean_version": lean_version,
        "build_command": build_command,
        "selected_modules_built_before_audit": True,
        "all_source_modules_selected": all_source_modules_selected,
        "selected_sources_unchanged_during_audit": True,
        "declaration_discovery": "Supported named theorem/lemma commands; unsupported syntax fails closed.",
    }
    record_path.write_text(json.dumps(record, indent=2) + "\n")
    print(f"PASS: {len(declarations)} theorems/lemmas in {len(sources)} built modules; allowed axioms only.")
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--name", required=True)
    parser.add_argument("--module", action="append", required=True)
    args = parser.parse_args()
    try:
        audit_modules(Path(__file__).resolve().parent, args.name, args.module)
    except (AuditError, OSError) as exc:
        parser.exit(1, f"Audit failed: {exc}\n")


if __name__ == "__main__":
    main()
