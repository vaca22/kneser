import Kneser.CrossMovingPreparationCompatibility
import Kneser.ActualHigherFinitePacket
import Kneser.ActualNormalizationAnchorExpansion

/-! Arbitrary finite expansions on the actual overlap gate with the true
real normalization anchor.  The root-dependent preparation constants
cancel by a proved cross-family telescoping identity. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Kneser.ActualRealAnchorHigherGate

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ActualBilateralGate Kneser.ActualGateAbel Kneser.HigherGateSeeds
open Kneser.CommonQuadraticBaseline Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open Kneser.ReflectedOrbitChainCoefficient Kneser.HigherGateIntegerRemainder
open Kneser.CrossMovingPreparationCompatibility Kneser.FiniteExpansionHolomorphy
open Kneser.RealNormalizationAnchor Kneser.PreparedActualFirstOrder
open scoped Topology BigOperators

def anchorSeed (M L : ℕ) (p : ℂ × ℂ) : ℂ := orbit normalizationAnchor p.1 (M + L)

def normalizedCoordinate (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N M : ℕ) (s : ℝ) (u : ℂ) : ℂ :=
  forwardCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) N u s -
    Kneser.ActualNormalizationAnchorExpansion.anchorValue
      U H (first (e 1)) (second (e 1)) A B (Γ 1) M s

def coefficient (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (n N M L j : ℕ) (u : ℂ) : ℂ :=
  HigherMovingPreparedCoordinate.movingCoefficient U H n (e n) A B (Γ n) (forwardSeed N L) u j -
    HigherMovingPreparedCoordinate.movingCoefficient U H n (e n) A B (Γ n) (anchorSeed M L) u j +
    if j = 0 then (M : ℂ) - (N : ℂ) else 0

theorem anchorSeed_analytic (M L : ℕ) (u : ℂ) : AnalyticAt ℂ (anchorSeed M L) (0, u) := by
  exact (ParabolicOverlapGate.analyticAt_forward_orbit_joint normalizationAnchor 0 (M + L)).comp_of_eq
    (analyticAt_fst.prod analyticAt_const) rfl

theorem anchorSeed_depth (R : ℝ) (M L : ℕ) (hR : 64 ≤ R)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re) (u : ℂ) :
    64 + (L : ℝ) / 2 ≤ (inverseCoordinate (anchorSeed M L (0, u))).re := by
  dsimp only [anchorSeed]
  rw [orbit_add, unfolding_orbit_zero_eq_iterate]
  have hh := iterate_inverse_re (orbit normalizationAnchor 0 M) (by linarith : 32 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re) L
  linarith

theorem polynomial_normalization (c d : ℕ → ℂ) (m : ℕ) (s q : ℂ) :
    (∑ j ∈ Finset.range (m + 1), s ^ j * (c j - d j + if j = 0 then q else 0)) =
      (∑ j ∈ Finset.range (m + 1), s ^ j * c j) -
        (∑ j ∈ Finset.range (m + 1), s ^ j * d j) + q := by
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp

/-- A fixed genuine gate and fixed genuine anchor entry serve all finite
orders.  The later petal length is selected before each compact subset. -/
theorem finite_real_anchor_expansion (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H (first (e 1)) (second (e 1)) A B K F (Γ 1))
    (hprep : ∀ n, Kneser.CommonPreparedFamily.Prepared A B F n (e n) (Γ n))
    (R : ℝ) (hR : 64 ≤ R)
    (hlocal : LocalAbelData U H (first (e 1)) (second (e 1)) A B (Γ 1) R)
    (N M : ℕ) (hN : R + 64 + 4 ≤ 3 * (N : ℝ) / 4)
    (hentry : R + 2 ≤ (inverseCoordinate (orbit normalizationAnchor 0 M)).re)
    (m n : ℕ) (hn : (m + 1) * (m + 1) + (m + 1) ≤ n) :
    ∃ L : ℕ, ∀ S : Set ℂ, IsCompact S → S ⊆ gate 64 N →
      (∀ u ∈ S, ∀ j ≤ m + 1,
        Summable (fun k => ‖termCoefficient
          (Kneser.HigherMovingOrbitDiscs.descendedTerm A B (Γ n) (n + 1) (forwardSeed N L) u) j k‖) ∧
        Summable (fun k => ‖termCoefficient
          (Kneser.HigherMovingOrbitDiscs.descendedTerm A B (Γ n) (n + 1) (anchorSeed M L) u) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
        ‖normalizedCoordinate U H A B e Γ N M s u -
          complexPolynomial (coefficient U H A B e Γ n N M L) (m + 1) (s : ℂ) u‖ ≤
            C * s ^ ((m + 1 : ℕ) + gamma (m + 1) (n + 1)) := by
  obtain ⟨hU, hU0, _hUd, hH, hHne, _hHlog, hA, hB, hA0, hB0,
    _he₁, _he₂, _hF, _hΓ₁, _hEven₁, hK0, hK, _hq, _hroots, hfactor, _hp₁, _hresidue⟩ := hdata
  have hKne : K 0 0 ≠ 0 := by rw [hK0]; norm_num
  obtain ⟨he, hΓ, hEven, _hp⟩ := hprep n
  obtain ⟨_he₁, hΓ₁, _hEven₁, hp₁⟩ := hprep 1
  obtain ⟨Ra, hRa, ha⟩ := HigherMovingPreparedCoordinate.exists_moving_higher_expansion
    U H A B K (Γ n) n (e n) hU hU0 hH hHne he hA hB hA0 hB0 hΓ
      (fun x v => hEven (x, v)) hK hKne hfactor (m + 1) (by omega) (by omega)
  obtain ⟨Rc, _hRc, hc⟩ := Kneser.PreparedDegreeCompatibility.exists_actual_normalized_compatibility
    U H A B K F (Γ n) (Γ 1) n 1 (e n) (e 1) hK hKne hfactor hΓ hΓ₁ (hprep n).2.2.2 hp₁
  let T := max Ra Rc
  have hT : 0 < T := hRa.trans_le (le_max_left _ _)
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * (T + 2))
  have hLT : T + 2 ≤ 64 + (L : ℝ) / 2 := by linarith
  have hN64 : (130 : ℝ) ≤ 3 * (N : ℝ) / 4 := by linarith
  refine ⟨L, ?_⟩
  intro S hS hSg
  have hWg : ∀ u ∈ S, AnalyticAt ℂ (forwardSeed N L) (0, u) := fun u _ => forwardSeed_analytic N L u
  have hWa : ∀ u ∈ S, AnalyticAt ℂ (anchorSeed M L) (0, u) := fun u _ => anchorSeed_analytic M L u
  have hdg : ∀ u ∈ S, T + 2 ≤ (inverseCoordinate (forwardSeed N L (0, u))).re :=
    fun u hu => hLT.trans (forwardSeed_depth N L hN64 u (hSg hu))
  have hda : ∀ u ∈ S, T + 2 ≤ (inverseCoordinate (anchorSeed M L (0, u))).re :=
    fun u _ => hLT.trans (anchorSeed_depth R M L hR hentry u)
  obtain ⟨hsg, Cg, hCg, heg⟩ := ha (forwardSeed N L) S hS hWg (fun u hu => by linarith [hdg u hu, le_max_left Ra Rc])
  obtain ⟨hsa, Ca, hCa, hea⟩ := ha (anchorSeed M L) S hS hWa (fun u hu => by linarith [hda u hu, le_max_left Ra Rc])
  have hcomp := moving_cross_compatibility
    (Kneser.PreparedDegreeCompatibility.preparedSeries U H n (e n) A B (Γ n))
    (Kneser.PreparedDegreeCompatibility.preparedSeries U H 1 (e 1) A B (Γ 1))
    T hT (hc T (le_max_right _ _)) (forwardSeed N L) (anchorSeed M L) S hS hWg hWa hdg hda
  have hbaseg : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (forwardSeed N 0 (0, u))).re := by
    intro u hu
    have hh := gate_forward_entry u N (R + 1) (by linarith) (hSg hu)
    have hh' : R + 1 + 1 < (inverseCoordinate (orbit u 0 N)).re := hh
    simpa only [forwardSeed, orbit_zero] using (show R + 2 ≤ (inverseCoordinate (orbit u 0 N)).re from by linarith)
  have hbasea : ∀ u ∈ S, R + 2 ≤ (inverseCoordinate (anchorSeed M 0 (0, u))).re := by
    intro u _
    simpa [anchorSeed] using hentry
  have habelg := forward_iterated_abel_uniform
    (fun s u => actualPreparedCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) u s)
    R hR hlocal.attracting (forwardSeed N 0) S hS
      (fun u _ => forwardSeed_analytic N 0 u) hbaseg L
  have habela := forward_iterated_abel_uniform
    (fun s u => actualPreparedCoordinate U H (first (e 1)) (second (e 1)) A B (Γ 1) u s)
    R hR hlocal.attracting (anchorSeed M 0) S hS
      (fun u _ => anchorSeed_analytic M 0 u) hbasea L
  refine ⟨(fun u hu j hj => ⟨hsg u hu j hj, hsa u hu j hj⟩), Cg + Ca, by positivity, ?_⟩
  filter_upwards [heg, hea, hcomp, habelg, habela] with s hEg hEa hC hAg hAa u hu
  have heq : normalizedCoordinate U H A B e Γ N M s u =
      HigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (forwardSeed N L) u s -
        HigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (anchorSeed M L) u s +
        ((M : ℂ) - (N : ℂ)) := by
    rw [HigherMovingPreparedCoordinate.movingCoordinate_eq, HigherMovingPreparedCoordinate.movingCoordinate_eq,
      hC u hu, attracting_series_one, attracting_series_one]
    have hg := hAg u hu
    have ha := hAa u hu
    simp only [forwardSeed, anchorSeed, orbit_zero, Nat.add_zero] at hg ha ⊢
    rw [orbit_add, hg, ha]
    dsimp [normalizedCoordinate, forwardCoordinate, Kneser.ActualNormalizationAnchorExpansion.anchorValue]
    ring
  rw [heq]
  unfold complexPolynomial coefficient
  rw [polynomial_normalization]
  have hb := (norm_sub_le
    (HigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (forwardSeed N L) u s -
      ∑ j ∈ Finset.range (m + 1 + 1), (s : ℂ) ^ j *
        HigherMovingPreparedCoordinate.movingCoefficient U H n (e n) A B (Γ n) (forwardSeed N L) u j)
    (HigherMovingPreparedCoordinate.movingCoordinate U H n (e n) A B (Γ n) (anchorSeed M L) u s -
      ∑ j ∈ Finset.range (m + 1 + 1), (s : ℂ) ^ j *
        HigherMovingPreparedCoordinate.movingCoefficient U H n (e n) A B (Γ n) (anchorSeed M L) u j)).trans
    (add_le_add (hEg u hu) (hEa u hu))
  convert hb using 1
  all_goals solve | ring | (congr 1 <;> ring)

end Kneser.ActualRealAnchorHigherGate
