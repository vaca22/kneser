import Kneser.ActualResidueSum
import Kneser.ExponentialMultiplierSecondOrder

/-! The actual removable multiplier-residue sum has constant value 1/3. -/

noncomputable section
namespace Kneser.ActualResidueValue

open Filter Kneser.ActualResidueSum Kneser.ExponentialPreparedModel
open Kneser.ExponentialUnfolding Kneser.ExponentialCuspParameter
open Kneser.ExponentialMultiplierSecondOrder Kneser.ReflectedOrbitChainCoefficient
open scoped Topology

theorem cusp_of_actual_root (U : ℂ → ℂ) (x : ℂ)
    (hx : unfolding (x ^ 2) (U x) = U x) :
    cuspParameter (rootMultiplier U x - 1) = x ^ 2 := by
  let v := rootMultiplier U x - 1
  have ht : -x ^ 2 + (1 - x ^ 2) * U x = v := by
    dsimp [v, rootMultiplier]
    ring
  have he : Complex.exp v = 1 + U x := by
    unfold unfolding at hx
    rw [ht] at hx
    linear_combination hx
  have hp : (1 + U x) * Complex.exp (-v) = 1 := by
    rw [← he, ← Complex.exp_add]
    simp
  change 1 - (1 + v) * Complex.exp (-v) = x ^ 2
  calc
    _ = 1 - (1 - x ^ 2) * ((1 + U x) * Complex.exp (-v)) := by
      dsimp [v, rootMultiplier]
      ring
    _ = _ := by rw [hp]; ring

theorem actual_removableResidue_zero
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    removableResidue H 0 = 1 / 3 := by
  rcases hdata with ⟨hU, hU0, _hUd, hH, hHne, hHlog, _hA, _hB, _hA0, _hB0,
    _he₁, _he₂, _hF, _hΓ, _hEven, _hK0, _hK, _hq, hroots, _hfactor, _hprep, _hresidue⟩
  let V : ℂ → ℂ := fun x => rootMultiplier U x - 1
  have hV : AnalyticAt ℂ V 0 := (analyticAt_rootMultiplier hU).sub analyticAt_const
  have hV0 : V 0 = 0 := by simp [V, rootMultiplier, hU0]
  have hVsquare : ∀ᶠ x in 𝓝 (0 : ℂ), cuspParameter (V x) = x ^ 2 :=
    hroots.mono (fun x hx => cusp_of_actual_root U x hx.1)
  obtain ⟨α, γ, R, hR, hα, _hαγ, hlog⟩ :=
    exists_branch_log_cubic_coefficients V hV hV0 hVsquare
  let J : ℂ → ℂ := fun x => α - x / 3 + γ * x ^ 2 + x ^ 3 * R x
  have hJ : AnalyticAt ℂ J 0 := by dsimp [J]; fun_prop
  have hHJ : H =ᶠ[𝓝 0] J := by
    apply cancel_power_eventually 1 H J hH.continuousAt hJ.continuousAt
    exact Eventually.of_forall (fun x => by
      have hh := hlog x
      rw [show 1 + V x = rootMultiplier U x by dsimp [V]; ring, hHlog] at hh
      simpa only [pow_one] using hh.trans (by dsimp [J]; ring))
  have hH0 : H 0 = α := by simpa [J] using hHJ.self_of_nhds
  have hJd : HasDerivAt J (-1 / 3) 0 := by
    have hd := (((hasDerivAt_id (0 : ℂ)).div_const 3).const_sub α).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).const_mul γ)
    have he := hd.add (((hasDerivAt_id (0 : ℂ)).pow 3).mul hR.hasStrictDerivAt.hasDerivAt)
    convert he using 1 <;> first | rfl | norm_num
  have hHd : HasDerivAt H (-1 / 3) 0 := hJd.congr_of_eventuallyEq hHJ
  have hg : HasDerivAt (fun x => (H x)⁻¹) (1 / 6) 0 := by
    have hh := hHd.inv hHne
    have hc : -(-1 / 3 : ℂ) / H 0 ^ 2 = 1 / 6 := by rw [hH0, hα]; norm_num
    rw [hc] at hh
    exact hh
  have hgn : HasDerivAt (fun x => (H (-x))⁻¹) (-1 / 6) 0 := by
    convert hg.comp_of_eq 0 (hasDerivAt_id (0 : ℂ)).neg (by simp) using 1 <;>
      first | rfl | norm_num
  have hN : HasDerivAt (residueNumerator H) (1 / 3) 0 := by
    convert hg.sub hgn using 1 <;> first | rfl | ring
  simpa [removableResidue] using hN.deriv

/-- A numerical bound follows from the proved value 1/3 and analyticity,
uniformly for the true ordered real roots. -/
theorem exists_actual_residue_unit_bound
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ η s₀ : ℝ, 0 < η ∧ 0 < s₀ ∧ η ≤ 1 / 4 ∧ s₀ ≤ 1 / 2 ∧
      ∀ s a b : ℝ, 0 < s → s < s₀ → |a| < η → |b| < η → a < 0 → 0 < b →
        unfolding s a = (a : ℂ) → unfolding s b = (b : ℂ) →
        ‖(Real.log (Kneser.PositiveKoenigsOrbit.multiplier s a) : ℂ)⁻¹ +
          (Real.log (Kneser.PositiveKoenigsOrbit.multiplier s b) : ℂ)⁻¹‖ ≤ 1 := by
  obtain ⟨η, sm, C, hη, hsm, _hC, hηq, hsmhalf, hpair⟩ :=
    exists_actual_residue_bound U H e₁ e₂ A B K F Γ hdata
  have hH := hdata.2.2.2.1
  have hHne := hdata.2.2.2.2.1
  have hR := analyticAt_removableResidue H hH hHne
  have hz : ‖removableResidue H 0‖ < (1 : ℝ) := by
    rw [actual_removableResidue_zero U H e₁ e₂ A B K F Γ hdata]
    norm_num
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp
    (hR.continuousAt.norm.eventually (gt_mem_nhds hz))
  refine ⟨η, min sm δ, hη, lt_min hsm hδ, hηq,
    (min_le_left _ _).trans hsmhalf, ?_⟩
  intro s a b hs hss ha hb ha0 hb0 hfa hfb
  have hp := (hpair s a b hs (hss.trans_le (min_le_left _ _)) ha hb ha0 hb0 hfa hfb).1
  rw [← hp]
  apply (hδbound (y := (s : ℂ)) ?_).le
  simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using
    hss.trans_le (min_le_right _ _)

end Kneser.ActualResidueValue
