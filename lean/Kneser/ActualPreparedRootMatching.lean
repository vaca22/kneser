import Kneser.ReflectedOrbitChainCoefficient
import Kneser.ActualRootPolynomialOrbit
import Kneser.RealExponentialRoots

/-!
The same actual preparation roots match the two ordered real fixed points.
Reality is obtained from the actual real roots and the monic quadratic;
the analytic square-root branches are not assumed real or ordered.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualPreparedRootMatching

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ReflectedOrbitChainCoefficient Kneser.ActualRootPolynomialOrbit
open scoped Topology

theorem roots_match_of_factor (U A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (hq : ∀ x u, rootPolynomial A B (x ^ 2) u = (u - U x) * (u - U (-x)))
    (s a b : ℝ) (x : ℂ) (hx : x ^ 2 = (s : ℂ)) (hab : a < b)
    (hfactor : ∀ u, unfolding s u - u = rootPolynomial A B s u * K s u)
    (ha : unfolding s a = (a : ℂ)) (hb : unfolding s b = (b : ℂ))
    (hKa : K s a ≠ 0) (hKb : K s b ≠ 0) :
    (U x = (a : ℂ) ∧ U (-x) = (b : ℂ)) ∨
      (U x = (b : ℂ) ∧ U (-x) = (a : ℂ)) := by
  have hqa : rootPolynomial A B (x ^ 2) a = 0 := by
    have h := hfactor a
    rw [ha, sub_self] at h
    rw [hx]
    exact (mul_eq_zero.mp h.symm).resolve_right hKa
  have hqb : rootPolynomial A B (x ^ 2) b = 0 := by
    have h := hfactor b
    rw [hb, sub_self] at h
    rw [hx]
    exact (mul_eq_zero.mp h.symm).resolve_right hKb
  rw [hq] at hqa hqb
  have haU := mul_eq_zero.mp hqa
  have hbU := mul_eq_zero.mp hqb
  have habne : (a : ℂ) ≠ (b : ℂ) := by exact_mod_cast ne_of_lt hab
  obtain ha₁ | ha₂ := haU <;> obtain hb₁ | hb₂ := hbU
  · exact False.elim (habne ((sub_eq_zero.mp ha₁).trans (sub_eq_zero.mp hb₁).symm))
  · exact Or.inl ⟨(sub_eq_zero.mp ha₁).symm, (sub_eq_zero.mp hb₂).symm⟩
  · exact Or.inr ⟨(sub_eq_zero.mp hb₁).symm, (sub_eq_zero.mp ha₂).symm⟩
  · exact False.elim (habne ((sub_eq_zero.mp ha₂).trans (sub_eq_zero.mp hb₂).symm))

/-- On a genuine common small parameter/spatial neighborhood, every pair
of ordered actual real roots matches the same analytic preparation. -/
theorem exists_root_matching_neighborhood
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ δ s₀ : ℝ, 0 < δ ∧ 0 < s₀ ∧
      ∀ s a b : ℝ, 0 < s → s < s₀ → |a| < δ → |b| < δ → a < b →
        unfolding s a = (a : ℂ) → unfolding s b = (b : ℂ) →
        ∀ x : ℂ, x ^ 2 = (s : ℂ) →
          (U x = (a : ℂ) ∧ U (-x) = (b : ℂ)) ∨
          (U x = (b : ℂ) ∧ U (-x) = (a : ℂ)) := by
  rcases hdata with ⟨_hU, _hU0, _hUd, _hH, _hHne, _hHlog, _hA, _hB, _hA0, _hB0,
    _he₁, _he₂, _hF, _hΓ, _hEven, hK0, hK, hq, _hroots, hfactor, _hprepared, _hresidue⟩
  have hKne : K 0 0 ≠ 0 := by rw [hK0]; norm_num
  obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp
    (hK.eventually (eventually_ne_nhds hKne))
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.mp hfactor
  refine ⟨ε / 2, min (ε / 2) r, by positivity, lt_min (by positivity) hr, ?_⟩
  intro s a b hs hss ha hb hab hfa hfb x hx
  have hsε : s < ε := by have h := hss.trans_le (min_le_left _ _); linarith
  have hsr : s < r := hss.trans_le (min_le_right _ _)
  have hKa : K s a ≠ 0 := by
    apply hεball (y := ((s : ℂ), (a : ℂ)))
    rw [Prod.dist_eq]
    change max (dist (s : ℂ) 0) (dist (a : ℂ) 0) < ε
    simp only [Prod.dist_eq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs]
    exact max_lt hsε (by linarith)
  have hKb : K s b ≠ 0 := by
    apply hεball (y := ((s : ℂ), (b : ℂ)))
    rw [Prod.dist_eq]
    change max (dist (s : ℂ) 0) (dist (b : ℂ) 0) < ε
    simp only [Prod.dist_eq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hs]
    exact max_lt hsε (by linarith)
  have hf : ∀ u, unfolding s u - u = rootPolynomial A B s u * K s u :=
    hrball (by simpa [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsr)
  exact roots_match_of_factor U A B K hq s a b x hx hab hf hfa hfb hKa hKb

/-- The actual ordered real roots are outputs. Their unordered matching
with the same preparation is uniform for all sufficiently small s>0. -/
theorem exists_actual_ordered_matched_roots
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
        unfolding s a = (a : ℂ) ∧ unfolding s b = (b : ℂ) ∧
        ∀ x : ℂ, x ^ 2 = (s : ℂ) →
          (U x = (a : ℂ) ∧ U (-x) = (b : ℂ)) ∨
          (U x = (b : ℂ) ∧ U (-x) = (a : ℂ)) := by
  obtain ⟨δ, s₁, hδ, hs₁, hmatch⟩ := exists_root_matching_neighborhood U H e₁ e₂ A B K F Γ hdata
  obtain ⟨s₂, hs₂, _hs₂half, hroots⟩ := RealExponentialRoots.exists_ordered_small_real_roots δ hδ
  refine ⟨min s₁ s₂, lt_min hs₁ hs₂, ?_⟩
  intro s hs hss
  obtain ⟨a, b, haδ, ha0, hb0, hbδ, hfa, hfb⟩ := hroots s hs (hss.trans_le (min_le_right _ _))
  refine ⟨a, b, ha0, hb0, hfa, hfb, ?_⟩
  apply hmatch s a b hs (hss.trans_le (min_le_left _ _))
  · rw [abs_of_neg ha0]; linarith
  · rw [abs_of_pos hb0]; exact hbδ
  · linarith
  · exact hfa
  · exact hfb

end Kneser.ActualPreparedRootMatching
end
