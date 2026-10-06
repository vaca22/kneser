import Kneser.ReflectedOrbitChainCoefficient
import Kneser.ActualPreparedSpatialHolomorphy

/-!
Spatial holomorphy of the actual reflected prepared coordinate follows
from the genuine logarithmic inverse iterates and a normally convergent
shifted residual series, on a common positive-parameter interval.
-/

noncomputable section

namespace Kneser.ReflectedPreparedSpatialHolomorphy

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ParabolicExponentialOrbit Kneser.RepellingExponentialOrbit
open Kneser.ReflectedEvenOrbitDiscs Kneser.ReflectedPreparedFirstOrder
open Kneser.PreparedSpatialHolomorphy Kneser.ReflectedOrbitChainCoefficient
open scoped Topology BigOperators

/-- The inverse iterates are spatially holomorphic along every orbit that
stays inside the actual principal-logarithm disc. -/
theorem differentiableAt_inverseOrbit_spatial (s v : ℂ) (k : ℕ)
    (hsmall : ∀ j : ℕ, ‖inverseOrbit v s j‖ < 1) :
    DifferentiableAt ℂ (fun u => inverseOrbit u s k) v := by
  induction k with
  | zero => exact differentiableAt_id
  | succ k ih =>
    have hslit : 1 - inverseOrbit v s k ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.sub_re, Complex.one_re]
      linarith [Complex.re_le_norm (inverseOrbit v s k), hsmall k]
    have h := ((((differentiableAt_const (1 : ℂ)).sub ih).clog hslit).add_const s).neg.div_const (1 - s)
    convert h using 1 <;> first | rfl | (funext u; rw [inverseOrbit_succ]; rfl)

/-- The shifted actual inverse residual sum is spatially holomorphic and
uniformly convergent on a bounded initial petal.  Its orbit containment and
summable majorant are derived from the actual exponential factorization. -/
theorem exists_holomorphic_prepared_tail
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hΓa : AnalyticAt ℂ Γ 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ C : ℝ, 0 < s₀ ∧ 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        DifferentiableOn ℂ (fun v => ∑' k : ℕ, shiftedTerm A B Γ N v s k)
          (boundedPetal R Z) ∧
        TendstoUniformlyOn
          (fun J : ℕ => fun v => ∑ k ∈ Finset.range J, shiftedTerm A B Γ N v s k)
          (fun v => ∑' k : ℕ, shiftedTerm A B Γ N v s k) atTop (boundedPetal R Z) ∧
        ∀ v ∈ boundedPetal R Z, Summable (fun k => ‖shiftedTerm A B Γ N v s k‖) := by
  obtain ⟨η, hη, hΓball⟩ := Metric.eventually_nhds_iff.mp hΓa.eventually_analyticAt
  let ρ : ℝ := min (η / 2) (1 / 2)
  have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
  obtain ⟨R₁, hR₁, horbits⟩ :=
    ReflectedPreparedRealMajorant.eventually_actual_rootPolynomial_orbit_bound A B K
      hK hK0 hfactor ρ hρ
  obtain ⟨R₂, C, hR₂, hC, hmajorant⟩ :=
    ReflectedPreparedRealMajorant.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ) N hK hK0 hfactor
      (continuousAt_descendedFactor Γ hΓa.continuousAt)
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
  have hsmall : ∀ v ∈ boundedPetal R Z, ∀ k : ℕ, ‖inverseOrbit v s k‖ < 1 := by
    intro v hv k
    have hn := (hactual s hs hss₁ v hv.1.le hv.2.le k).2
    rw [norm_neg] at hn
    exact hn.trans ((min_le_right _ _).trans_lt (by norm_num))
  have hpoint : ∀ v ∈ boundedPetal R Z, ∀ k : ℕ,
      AnalyticAt ℂ Γ (Complex.sqrt (s : ℂ), -inverseOrbit v s k) := by
    intro v hv k
    have hn := (hactual s hs hss₁ v hv.1.le hv.2.le k).2
    have hη' : ρ < η := (min_le_left _ _).trans_lt (by linarith)
    apply hΓball (y := (Complex.sqrt (s : ℂ), -inverseOrbit v s k))
    simpa only [dist_zero_right, Prod.norm_def] using max_lt hsqrt (hn.trans hη')
  have hbound : ∀ k : ℕ, ∀ v ∈ boundedPetal R Z,
      ‖shiftedTerm A B Γ N v s k‖ ≤ C / ((k : ℝ) + 1) ^ (2 * N) := by
    intro k v hv
    have ht := hbounds s hs hss₂ v hv.1.le hv.2.le (k + 1)
    change ‖descendedTerm A B Γ N v (s : ℂ) (k + 1)‖ ≤ _
    rw [descendedTerm_eq]
    apply ht.trans
    apply div_le_div_of_nonneg_left hC (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) (2 * N)
  have hterms : ∀ k : ℕ, DifferentiableOn ℂ
      (fun v => shiftedTerm A B Γ N v s k) (boundedPetal R Z) := by
    intro k v hv
    have ho := (differentiableAt_inverseOrbit_spatial s v (k + 1) (hsmall v hv)).neg
    have hq : DifferentiableAt ℂ
        (fun u => rootPolynomial A B s (-inverseOrbit u s (k + 1))) v :=
      ((ho.pow 2).sub (ho.const_mul (A s))).add_const (B s)
    have hg := (hpoint v hv (k + 1)).differentiableAt.comp v
      ((differentiableAt_const (Complex.sqrt (s : ℂ))).prodMk ho)
    convert ((hq.pow N).mul hg).differentiableWithinAt using 1 <;>
      first | rfl | (funext u; simp only [shiftedTerm, descendedTerm, splitTerm,
        AnalyticEvenDescent.square_sqrt]; rfl)
  have hsum := Complex.differentiableOn_tsum_of_summable_norm
    (summable_parabolic_majorant C (q := 2 * N) (by omega)) hterms
    (boundedPetal_isOpen hRpos) hbound
  have huni := tendstoUniformlyOn_tsum
    (summable_parabolic_majorant C (q := 2 * N) (by omega)) hbound
  refine ⟨hsum, ?_, ?_⟩
  · intro v hv
    exact (tendsto_finset_range : Tendsto Finset.range atTop atTop).eventually (huni v hv)
  · intro v hv
    exact summable_norm_of_parabolic_bound _ C (q := 2 * N) (by omega)
      (fun k => hbound k v hv)

/-- The full actual reflected prepared coordinate is holomorphic in the
initial point.  Both logarithm branches are controlled by the actual small
root branches, rather than supplied as hypotheses. -/
theorem exists_holomorphic_actualInversePreparedCoordinate
    (U H e₁ e₂ A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hΓa : AnalyticAt ℂ Γ 0) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ C : ℝ, 0 < s₀ ∧ 0 ≤ C ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        DifferentiableOn ℂ (fun v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s)
          (boundedPetal R Z) ∧
        TendstoUniformlyOn
          (fun J : ℕ => fun v => ∑ k ∈ Finset.range J, shiftedTerm A B Γ 2 v s k)
          (fun v => ∑' k : ℕ, shiftedTerm A B Γ 2 v s k) atTop (boundedPetal R Z) ∧
        ∀ v ∈ boundedPetal R Z, Summable (fun k => ‖shiftedTerm A B Γ 2 v s k‖) := by
  obtain ⟨R₀, hR₀, htail⟩ := exists_holomorphic_prepared_tail A B K Γ 2 (by norm_num)
    hK hK0 hfactor hΓa
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR Z hZ
  have hRpos : 0 < R := hR₀.trans_le hR
  obtain ⟨s₁, C, hs₁, hC, ht⟩ := htail R hR Z hZ
  obtain ⟨s₂, hs₂, hm⟩ := ActualPreparedSpatialHolomorphy.exists_holomorphic_preparedModelTime
    hU.neg (by simp only [Pi.neg_apply, hU0, neg_zero]) (H := -H) (e₁ := e₁) (e₂ := -e₂)
    R Z hRpos hZ
  refine ⟨min s₁ s₂, C, lt_min hs₁ hs₂, hC, ?_⟩
  intro s hs hss
  obtain ⟨hhol, huni, hsum⟩ := ht s hs (hss.trans_le (min_le_left _ _))
  have hmodel := hm s hs (hss.trans_le (min_le_right _ _))
  refine ⟨?_, huni, hsum⟩
  convert hmodel.add hhol using 1 <;> rfl

/-- One spatial holomorphy interval applies on each bounded petal, together
with uniform convergence and absolute convergence of the actual correction. -/
def SpatialHolomorphy (U H e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (R₀ : ℝ) : Prop :=
  ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
      DifferentiableOn ℂ (fun v => actualInversePreparedCoordinate U H e₁ e₂ A B Γ v s)
        (boundedPetal R Z) ∧
      TendstoUniformlyOn
        (fun J : ℕ => fun v => ∑ k ∈ Finset.range J, shiftedTerm A B Γ 2 v s k)
        (fun v => ∑' k : ℕ, shiftedTerm A B Γ 2 v s k) atTop (boundedPetal R Z) ∧
      ∀ v ∈ boundedPetal R Z, Summable (fun k => ‖shiftedTerm A B Γ 2 v s k‖)

set_option maxHeartbeats 1000000 in
/-- A single constructed set of actual exponential witnesses has both
spatially holomorphic prepared coordinates and the absolutely convergent
explicit first-order coefficient, uniformly on compact initial petal sets. -/
theorem exists_actual_holomorphic_repelling_explicit_coefficient :
    ∃ U H e₁ e₂ A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F Γ : ℂ × ℂ → ℂ,
      ActualPreparationData U H e₁ e₂ A B K F Γ ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧
        UniformRepellingFirstOrder.CompactFirstOrder U H e₁ e₂ A B Γ R₀ ∧
        (∀ v, R₀ + 1 ≤ (inverseCoordinate v).re → ∀ k,
          deriv (fun s => shiftedTerm A B Γ 2 v s k) 0 = explicitTerm A B Γ v k) ∧
        ExplicitCompactFirstOrder U H e₁ e₂ A B Γ R₀ ∧
        SpatialHolomorphy U H e₁ e₂ A B Γ R₀ := by
  obtain ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata, Rc, hRc, hcompact, hchain, hexplicit⟩ :=
    exists_actual_compact_repelling_explicit_coefficient
  have hdata' := hdata
  rcases hdata with ⟨hU, hU0, hUd, hH, hHne, hHlog, hA, hB, hA0, hB0, he₁, he₂,
    hF, hΓ, hΓeven, hK0, hK, hq, hroots, hfactor, hprepared, hresidue⟩
  obtain ⟨Rh, hRh, hspatial⟩ := exists_holomorphic_actualInversePreparedCoordinate
    U H e₁ e₂ A B K Γ hU hU0 hK (by rw [hK0]; norm_num) hfactor hΓ
  let R₀ : ℝ := max Rc Rh
  have hR₀ : 0 < R₀ := hRc.trans_le (le_max_left _ _)
  have hlower : ∀ S : Set ℂ, (∀ v ∈ S, R₀ + 1 ≤ (inverseCoordinate v).re) →
      ∀ v ∈ S, Rc + 1 ≤ (inverseCoordinate v).re := by
    intro S hp v hv
    have hle : Rc ≤ R₀ := le_max_left _ _
    linarith [hp v hv]
  refine ⟨U, H, e₁, e₂, A, B, K, F, Γ, hdata', R₀, hR₀, ?_, ?_, ?_, ?_⟩
  · intro S hS hp
    exact hcompact S hS (hlower S hp)
  · intro v hv
    apply hchain v
    have hle : Rc ≤ R₀ := le_max_left _ _
    linarith
  · intro S hS hp
    exact hexplicit S hS (hlower S hp)
  · intro R hR Z hZ
    obtain ⟨s₀, C, hs₀, hC, hfull⟩ := hspatial R ((le_max_right _ _).trans hR) Z hZ
    exact ⟨s₀, hs₀, hfull⟩

end Kneser.ReflectedPreparedSpatialHolomorphy

end
