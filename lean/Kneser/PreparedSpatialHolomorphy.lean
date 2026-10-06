import Kneser.ActualRootPolynomialOrbit
import Kneser.EvenPreparedOrbitDiscs
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
The actual positive-parameter prepared residual series is holomorphic in the
initial point, with uniform convergence on a bounded parabolic petal.  These
properties follow from the constructed analytic factors and true orbits.
-/

noncomputable section

namespace Kneser.PreparedSpatialHolomorphy

open Filter Set Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ParabolicExponentialOrbit Kneser.EvenPreparedOrbitDiscs
open scoped Topology BigOperators

def boundedPetal (R Z : ℝ) : Set ℂ :=
  {u | R + 1 < (inverseCoordinate u).re ∧ ‖inverseCoordinate u‖ < Z}

theorem boundedPetal_isOpen {R Z : ℝ} (hR : 0 < R) : IsOpen (boundedPetal R Z) := by
  rw [isOpen_iff_mem_nhds]
  intro u hu
  have hune : u ≠ 0 := by
    intro heq
    simp [boundedPetal, heq, inverseCoordinate] at hu
    linarith [hu.1]
  have hi : ContinuousAt inverseCoordinate u := continuousAt_const.div continuousAt_id hune
  exact (Complex.continuous_re.continuousAt.comp hi).eventually (lt_mem_nhds hu.1) |>.and
    (hi.norm.eventually (gt_mem_nhds hu.2))

theorem differentiable_orbit_spatial (s : ℂ) (k : ℕ) :
    Differentiable ℂ (fun u => orbit u s k) := by
  induction k with
  | zero =>
    convert (differentiable_id : Differentiable ℂ (id : ℂ → ℂ)) using 1 <;> rfl
  | succ k ih =>
    have h := ((differentiable_const (-s)).add
      ((differentiable_const (1 - s)).mul ih)).cexp.sub_const 1
    convert h using 1 <;> rfl

/-- Spatial holomorphy and uniform summability of the actual prepared tail
hold throughout a common positive-parameter interval. -/
theorem exists_holomorphic_prepared_tail
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hΓa : AnalyticAt ℂ Γ 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ C : ℝ, 0 < s₀ ∧ 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        DifferentiableOn ℂ (fun u => ∑' k : ℕ, descendedTerm A B Γ N u s k)
          (boundedPetal R Z) ∧
        TendstoUniformlyOn
          (fun J : ℕ => fun u => ∑ k ∈ Finset.range J, descendedTerm A B Γ N u s k)
          (fun u => ∑' k : ℕ, descendedTerm A B Γ N u s k) atTop (boundedPetal R Z) ∧
        ∀ u ∈ boundedPetal R Z, Summable (fun k => ‖descendedTerm A B Γ N u s k‖) := by
  obtain ⟨η, hη, hΓball⟩ := Metric.eventually_nhds_iff.mp hΓa.eventually_analyticAt
  obtain ⟨R₁, hR₁, horbits⟩ :=
    ActualRootPolynomialOrbit.eventually_actual_rootPolynomial_orbit_bound A B K hK hK0
      hfactor (η / 2) (by positivity)
  obtain ⟨R₂, C, hR₂, hC, hmajorant⟩ :=
    ActualRootPolynomialOrbit.exists_actual_prepared_real_majorant A B K (descendedFactor Γ) N
      hK hK0 hfactor (continuousAt_descendedFactor Γ hΓa.continuousAt)
  refine ⟨max R₁ R₂, hR₁.trans_le (le_max_left _ _), ?_⟩
  intro R hR Z hZ
  have hRpos : 0 < R := hR₁.trans_le ((le_max_left _ _).trans hR)
  obtain ⟨s₁, hs₁, hactual⟩ := horbits R ((le_max_left _ _).trans hR) Z hZ
  obtain ⟨s₂, hs₂, hbounds⟩ := hmajorant R ((le_max_right _ _).trans hR) Z hZ
  refine ⟨min s₁ (min s₂ (η ^ 2 / 4)), C,
    lt_min hs₁ (lt_min hs₂ (by positivity)), hC, ?_⟩
  intro s hs hss
  have hss₁ : s < s₁ := hss.trans_le (min_le_left _ _)
  have hss₂ : s < s₂ := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsη : s < η ^ 2 / 4 := hss.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsqrt : ‖Complex.sqrt (s : ℂ)‖ < η := by
    have hsq : ‖Complex.sqrt (s : ℂ)‖ ^ 2 = s := by
      rw [← norm_pow, AnalyticEvenDescent.square_sqrt, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hs]
    nlinarith [norm_nonneg (Complex.sqrt (s : ℂ))]
  have hpoint : ∀ u ∈ boundedPetal R Z, ∀ k : ℕ,
      AnalyticAt ℂ Γ (Complex.sqrt (s : ℂ), orbit u s k) := by
    intro u hu k
    have hv := (hactual s hs hss₁ u hu.1.le hu.2.le k).2
    apply hΓball (y := (Complex.sqrt (s : ℂ), orbit u s k))
    simpa only [dist_zero_right, Prod.norm_def] using max_lt hsqrt (hv.trans (by linarith))
  have hbound : ∀ k : ℕ, ∀ u ∈ boundedPetal R Z,
      ‖descendedTerm A B Γ N u s k‖ ≤ C / ((k : ℝ) + 1) ^ (2 * N) := by
    intro k u hu
    simpa only [descendedTerm_eq] using hbounds s hs hss₂ u hu.1.le hu.2.le k
  have hterms : ∀ k : ℕ, DifferentiableOn ℂ
      (fun u => descendedTerm A B Γ N u s k) (boundedPetal R Z) := by
    intro k u hu
    have ho := (differentiable_orbit_spatial s k).differentiableAt (x := u)
    have hq : DifferentiableAt ℂ (fun u => rootPolynomial A B s (orbit u s k)) u :=
      ((ho.pow 2).sub (ho.const_mul (A s))).add_const (B s)
    have hg := (hpoint u hu k).differentiableAt.comp u
      ((differentiableAt_const (Complex.sqrt (s : ℂ))).prodMk ho)
    convert ((hq.pow N).mul hg).differentiableWithinAt using 1 <;>
      first | rfl | (funext v; simp only [descendedTerm, splitTerm,
        AnalyticEvenDescent.square_sqrt]; rfl)
  have hsum := Complex.differentiableOn_tsum_of_summable_norm
    (summable_parabolic_majorant C (q := 2 * N) (by omega)) hterms
    (boundedPetal_isOpen hRpos) hbound
  have huni := tendstoUniformlyOn_tsum
    (summable_parabolic_majorant C (q := 2 * N) (by omega)) hbound
  refine ⟨hsum, ?_, ?_⟩
  · intro v hv
    exact (tendsto_finset_range : Tendsto Finset.range atTop atTop).eventually (huni v hv)
  · intro u hu
    exact summable_norm_of_parabolic_bound _ C (q := 2 * N) (by omega)
      (fun k => hbound k u hu)

end Kneser.PreparedSpatialHolomorphy

end
