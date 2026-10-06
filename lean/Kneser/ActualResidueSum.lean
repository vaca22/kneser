import Kneser.ActualKoenigsIdentification

/-!
The two singular multiplier residues cancel in the original parameter.
The removable germ is constructed by derivative slope and even descent;
its uniform bound is derived from the actual preparation.
-/

noncomputable section
namespace Kneser.ActualResidueSum

open Filter Kneser.ExponentialModelTime Kneser.AnalyticEvenDescent
open Kneser.ActualPreparedRootMatching Kneser.ActualKoenigsIdentification
open Kneser.ReflectedOrbitChainCoefficient Kneser.ExponentialPreparedModel
open Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.PositiveKoenigsOrbit
open scoped Topology

def residueNumerator (H : ℂ → ℂ) (x : ℂ) : ℂ := (H x)⁻¹ - (H (-x))⁻¹

def removableResidue (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  dslope (residueNumerator H) 0 (Complex.sqrt s)

theorem residueNumerator_zero (H : ℂ → ℂ) : residueNumerator H 0 = 0 := by
  simp [residueNumerator]

theorem residueNumerator_odd (H : ℂ → ℂ) (x : ℂ) :
    residueNumerator H (-x) = -residueNumerator H x := by
  simp only [residueNumerator, neg_neg]
  ring

theorem analyticAt_removableResidue (H : ℂ → ℂ) (hH : AnalyticAt ℂ H 0)
    (hHne : H 0 ≠ 0) : AnalyticAt ℂ (removableResidue H) 0 := by
  have hHn : AnalyticAt ℂ (fun x : ℂ => H (-x)) 0 :=
    hH.comp_of_eq analyticAt_id.neg (by simp)
  have hN : AnalyticAt ℂ (residueNumerator H) 0 :=
    (hH.inv hHne).sub (hHn.inv (by simpa using hHne))
  exact analyticAt_even_sqrt
    (dslope_odd_even (residueNumerator_zero H) (residueNumerator_odd H))
    (analyticAt_dslope_zero hN)

theorem removableResidue_square (H : ℂ → ℂ) (x : ℂ) (hx : x ≠ 0) :
    removableResidue H (x ^ 2) = (x * H x)⁻¹ + ((-x) * H (-x))⁻¹ := by
  unfold removableResidue
  rw [even_sqrt_square (dslope_odd_even (residueNumerator_zero H)
    (residueNumerator_odd H)), dslope_of_ne _ hx, slope_def_field,
    residueNumerator_zero]
  simp only [residueNumerator, sub_zero, mul_inv_rev, inv_neg, div_eq_mul_inv]
  ring

theorem actual_residue_of_matching (U H : ℂ → ℂ)
    (hHlog : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (s a b : ℝ) (x : ℂ) (hs1 : s < 1) (ha : -1 < a) (hb : 0 < b)
    (hx : x ^ 2 = (s : ℂ)) (hxne : x ≠ 0)
    (hm : (U x = (a : ℂ) ∧ U (-x) = (b : ℂ)) ∨
      (U x = (b : ℂ) ∧ U (-x) = (a : ℂ))) :
    removableResidue H s = (Real.log (multiplier s a) : ℂ)⁻¹ +
      (Real.log (multiplier s b) : ℂ)⁻¹ := by
  have hμa : 0 < multiplier s a := by
    dsimp [multiplier]
    exact mul_pos (by linarith) (by linarith)
  have hμb : 0 < multiplier s b := by
    dsimp [multiplier]
    exact mul_pos (by linarith) (by linarith)
  have hp := removableResidue_square H x hxne
  rw [hx, ← hHlog x, ← hHlog (-x)] at hp
  rcases hm with hm | hm
  · rw [rootMultiplier_of_real_value U s a x hx hm.1,
      rootMultiplier_of_real_value U s b (-x) (by simpa only [neg_sq] using hx) hm.2,
      ← Complex.ofReal_log hμa.le, ← Complex.ofReal_log hμb.le] at hp
    exact hp
  · rw [rootMultiplier_of_real_value U s b x hx hm.1,
      rootMultiplier_of_real_value U s a (-x) (by simpa only [neg_sq] using hx) hm.2,
      ← Complex.ofReal_log hμb.le, ← Complex.ofReal_log hμa.le] at hp
    exact hp.trans (add_comm _ _)

/-- The genuine sum of the two singular residues is uniformly bounded
for every sufficiently small actual ordered pair of fixed points. -/
theorem exists_actual_residue_bound
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ η s₀ C : ℝ, 0 < η ∧ 0 < s₀ ∧ 0 < C ∧ η ≤ 1 / 4 ∧ s₀ ≤ 1 / 2 ∧
      ∀ s a b : ℝ, 0 < s → s < s₀ → |a| < η → |b| < η → a < 0 → 0 < b →
        unfolding s a = (a : ℂ) → unfolding s b = (b : ℂ) →
        removableResidue H s = (Real.log (multiplier s a) : ℂ)⁻¹ +
          (Real.log (multiplier s b) : ℂ)⁻¹ ∧
        ‖(Real.log (multiplier s a) : ℂ)⁻¹ +
          (Real.log (multiplier s b) : ℂ)⁻¹‖ ≤ C := by
  obtain ⟨ηm, sm, hηm, hsm, hmatch⟩ :=
    exists_root_matching_neighborhood U H e₁ e₂ A B K F Γ hdata
  rcases hdata with ⟨_hU, _hU0, _hUd, hH, hHne, hHlog, _⟩
  have hR := analyticAt_removableResidue H hH hHne
  let C : ℝ := ‖removableResidue H 0‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hbound : ∀ᶠ s in 𝓝 (0 : ℂ), ‖removableResidue H s‖ < C :=
    hR.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hbound
  let η := min ηm (1 / 4)
  let s₀ := min sm (min δ (1 / 2))
  refine ⟨η, s₀, C, by dsimp [η]; positivity, by dsimp [s₀]; positivity,
    hC, min_le_right _ _, (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro s a b hs hss ha hb ha0 hb0 hfa hfb
  have hs1 : s < 1 := by
    have hh := hss.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have haa : -1 < a := by
    have hh := (abs_lt.mp ha).1
    have hηq : η ≤ 1 / 4 := min_le_right _ _
    linarith
  let x := Complex.sqrt (s : ℂ)
  have hx : x ^ 2 = (s : ℂ) := square_sqrt _
  have hxne : x ≠ 0 := by
    intro he
    have hz := hx
    rw [he, zero_pow (by norm_num : 2 ≠ 0)] at hz
    exact (by exact_mod_cast (ne_of_gt hs) : (s : ℂ) ≠ 0) hz.symm
  have hm := hmatch s a b hs (hss.trans_le (min_le_left _ _))
    (ha.trans_le (min_le_left _ _)) (hb.trans_le (min_le_left _ _))
    (by linarith) hfa hfb x hx
  have heq := actual_residue_of_matching U H hHlog s a b x hs1 haa hb0 hx hxne hm
  refine ⟨heq, ?_⟩
  rw [← heq]
  apply (hδbound (y := (s : ℂ)) ?_).le
  simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using
    hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))

end Kneser.ActualResidueSum
