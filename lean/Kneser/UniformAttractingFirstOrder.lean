import Kneser.PreparedActualFirstOrder
import Kneser.UniformFirstOrderCutoff
import Kneser.UniformModelTime
import Kneser.PreparedSpatialHolomorphy

/-!
Common first-order remainder constants over bounded sets of true initial
petal points.  The dynamical, preparation-disc and infinite-tail estimates
are discharged; only the supplied model's common disc bound is input to the
generic wrapper.
-/

noncomputable section

namespace Kneser.UniformAttractingFirstOrder

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.EvenPreparedOrbitDiscs Kneser.ParabolicExponentialOrbit
open scoped Topology

theorem prepared_quadratic_uniform_first_order
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∀ S : Set ℂ, (∀ u ∈ S, R + 1 ≤ (inverseCoordinate u).re ∧ ‖inverseCoordinate u‖ ≤ Z) →
      ∀ ψ : ℂ → ℂ → ℂ, ∀ r Mψ : ℝ, 0 < r → 0 ≤ Mψ →
        (∀ u ∈ S, DiffContOnCl ℂ (ψ u) (ball 0 r)) →
        (∀ u ∈ S, ∀ z ∈ sphere (0 : ℂ) r, ‖ψ u z‖ ≤ Mψ) →
        let term := fun u => descendedTerm A B Γ 2 u
        let X := fun u => coordinateSeries (fun s : ℝ => ψ u s) (fun s : ℝ => term u s)
        let d := fun u => firstOrderCoefficient (deriv (ψ u) 0)
          (fun k => deriv (fun z => term u z k) 0)
        ∃ C : ℝ, 0 ≤ C ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ‖X u s - X u 0 - s • d u‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
          (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ‖X u s - X u 0 - s • d u‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
          (∀ u ∈ S, Summable (fun k => ‖deriv (fun z => term u z k) 0‖)) ∧
          ∀ u ∈ S, HasDerivWithinAt (X u) (d u) (Ici 0) 0 := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := exists_uniform_prepared_orbit_disc_bounds A B Γ 2
    hAa hBa hA0 hB0 hΓa hEven
  obtain ⟨R₂, CT, hR₂, hCT, hreal⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K (descendedFactor Γ) 2
      hK hK0 hfactor (continuousAt_descendedFactor Γ hΓa.continuousAt)
  refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro R hR Z hZ S hS ψ r Mψ hr hMψ hψ hψbound
  dsimp only
  obtain ⟨c, M, hc, hM, hcommon⟩ := hdiscs R ((le_max_left _ _).trans hR) Z hZ
  obtain ⟨s₀, hs₀, hrealbounds⟩ := hreal R ((le_max_right _ _).trans hR) Z hZ
  have hdisc : ∀ u ∈ S, ∀ k, DiffContOnCl ℂ
      (fun z => descendedTerm A B Γ 2 u z k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)) := by
    intro u hu
    exact (hcommon u (by linarith [(hS u hu).1]) (hS u hu).2).1
  have hbound : ∀ u ∈ S, ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖descendedTerm A B Γ 2 u z k‖ ≤ M / ((k : ℝ) + 1) ^ 4 := by
    intro u hu
    exact (hcommon u (by linarith [(hS u hu).1]) (hS u hu).2).2
  have hterms : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, ∀ k,
      ‖descendedTerm A B Γ 2 u (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 4 := by
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
      (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss u hu k
    simpa only [descendedTerm_eq] using
      hrealbounds s hs hss u (hS u hu).1 (hS u hu).2 k
  have he := UniformFirstOrderCutoff.coordinate_expansion_from_uniform_term_discs
    S ψ (fun u => descendedTerm A B Γ 2 u) r Mψ c M CT hr hMψ hc hM hCT
    hψ hψbound hdisc hbound hterms
  let C := UniformFirstOrderCutoff.errorConstant r Mψ c M CT
  have hC : 0 ≤ C := UniformFirstOrderCutoff.errorConstant_nonneg r Mψ c M CT
    hr hc hMψ hM hCT
  refine ⟨C, hC, he.1, ?_, ?_, he.2⟩
  · have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ hs => hs.le).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [he.1, self_mem_nhdsWithin, hsmall] with s hs hpos hs1 u hu
    exact (hs u hu).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (show 0 < s from hpos) hs1 (by norm_num)) hC)
  · intro u hu
    exact summable_norm_of_parabolic_bound _ (M / c) (q := 2) (by norm_num)
      (N2FirstOrderCutoff.norm_deriv_term_le (descendedTerm A B Γ 2 u) c M hc
        (hdisc u hu) (hbound u hu))

/-- Compact initial sets have one common model disc and one common full
first-order remainder bound for the actual constructed model. -/
theorem prepared_model_compact_first_order
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he₁ : AnalyticAt ℂ e₁ 0) (he₂ : AnalyticAt ℂ e₂ 0)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ S : Set ℂ, IsCompact S →
      (∀ u ∈ S, R₀ + 1 ≤ (inverseCoordinate u).re) →
      ∃ C : ℝ, 0 ≤ C ∧
        (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
          ‖PreparedActualFirstOrder.actualPreparedCoordinate U H e₁ e₂ A B Γ u s -
            PreparedActualFirstOrder.actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 -
            s • PreparedActualFirstOrder.actualPreparedCoefficient U H e₁ e₂ A B Γ u‖ ≤
            C * s ^ (6 / 5 : ℝ)) ∧
        (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
          ‖PreparedActualFirstOrder.actualPreparedCoordinate U H e₁ e₂ A B Γ u s -
            PreparedActualFirstOrder.actualPreparedCoordinate U H e₁ e₂ A B Γ u 0 -
            s • PreparedActualFirstOrder.actualPreparedCoefficient U H e₁ e₂ A B Γ u‖ ≤
            C * s ^ (10 / 9 : ℝ)) ∧
        (∀ u ∈ S, Summable (fun k => ‖deriv (fun s => descendedTerm A B Γ 2 u s k) 0‖)) ∧
        ∀ u ∈ S, HasDerivWithinAt
          (PreparedActualFirstOrder.actualPreparedCoordinate U H e₁ e₂ A B Γ u)
          (PreparedActualFirstOrder.actualPreparedCoefficient U H e₁ e₂ A B Γ u) (Ici 0) 0 := by
  obtain ⟨R₀, hR₀, hcommon⟩ := prepared_quadratic_uniform_first_order A B K Γ
    hAa hBa hA0 hB0 hΓa hEven hK hK0 hfactor
  refine ⟨R₀, hR₀, ?_⟩
  intro S hS hpetal
  have hune : ∀ u ∈ S, u ≠ 0 := by
    intro u hu heq
    have h := hpetal u hu
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at h
    linarith
  have hi : ContinuousOn inverseCoordinate S := by
    intro u hu
    exact (continuousAt_const.div continuousAt_id (hune u hu)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hS.exists_bound_of_continuousOn hi
  let Z : ℝ := max Z₁ 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hSin : ∀ u ∈ S, R₀ + 1 ≤ (inverseCoordinate u).re ∧ ‖inverseCoordinate u‖ ≤ Z := by
    intro u hu
    exact ⟨hpetal u hu, (hZ₁ u hu).trans (le_max_left _ _)⟩
  have hneg : ∀ u ∈ S, u.re < 0 := by
    intro u hu
    have hp : 0 < (inverseCoordinate u).re := by linarith [hpetal u hu]
    simpa only [Complex.neg_re, neg_pos] using
      ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hp
  obtain ⟨r, Mψ, hr, hMψ, hmodel⟩ :=
    UniformModelTime.exists_compact_preparedModelTime_boundary_bounds
      hU hU0 hH hHne he₁ he₂ S hS hneg
  exact hcommon R₀ (le_refl _) Z hZ S hSin
    (fun u s => ExponentialModelTime.preparedModelTime U H e₁ e₂ s u) r Mψ hr hMψ
    (fun u hu => (hmodel u hu).1) (fun u hu => (hmodel u hu).2)

end Kneser.UniformAttractingFirstOrder

end
