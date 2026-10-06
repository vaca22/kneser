import Kneser.PerturbedExponentialOrbit
import Kneser.ParabolicOrbitSum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Cauchy decay estimates for the actual prepared orbit residual

The residual is defined as `q^N Γ` and is evaluated on the actual finite
exponential orbit. The orbit estimate and Cauchy inequality are theorems,
not hypotheses. Analyticity and bounds of the preparation factors on a fixed
polydisc remain explicit inputs of the preparation construction.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.PreparedResidualEstimates

open Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.PerturbedExponentialOrbit
open Complex Metric

/-- A fixed polydisc containing every orbit used in the Cauchy estimates. -/
def preparationPolydisc (Z : ℝ) : Set (ℂ × ℂ) :=
  (closedBall 0 (parameterRadius Z 0)) ×ˢ (closedBall 0 (1 / 2 : ℝ))

/-- The prepared residual is an actual product of its analytic factors. -/
def preparedResidual (q Γ : ℂ × ℂ → ℂ) (N : ℕ) (s v : ℂ) : ℂ :=
  q (s, v) ^ N * Γ (s, v)

/-- The numerical radius has precisely the `c/(k+1)²` form. -/
theorem parameterRadius_eq (Z : ℝ) (k : ℕ) :
    parameterRadius Z k = parameterRadius Z 0 / ((k : ℝ) + 1) ^ 2 := by
  simp [parameterRadius, div_eq_mul_inv]
  ring

/-- Actual finite orbit graphs stay in the fixed preparation polydisc. -/
theorem orbit_graph_mem_polydisc (u s : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (k : ℕ)
    (hs : ‖s‖ ≤ parameterRadius Z k) :
    (s, orbit u s k) ∈ preparationPolydisc Z := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hr0 := parameterRadius_pos Z hZ0 0
  have hden : 1 ≤ ((k : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hrle : parameterRadius Z k ≤ parameterRadius Z 0 := by
    rw [parameterRadius_eq]
    exact div_le_self hr0.le hden
  have horbit := finite_orbit_norm_bound_of_upper_bound u s R Z hR hu hZ k hs k (le_refl k)
  have hdenR : 0 < R + (k : ℝ) / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hsmall : ‖orbit u s k‖ ≤ 1 / 2 := by
    apply horbit.trans
    apply (div_le_iff₀ hdenR).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  exact ⟨by simpa [mem_closedBall, dist_zero_right] using hs.trans hrle,
    by simpa [mem_closedBall, dist_zero_right] using hsmall⟩

/-- The actual finite orbit decays like `4/(k+1)` throughout its parameter disc. -/
theorem finite_orbit_norm_le_four_div (u s : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (k : ℕ)
    (hs : ‖s‖ ≤ parameterRadius Z k) :
    ‖orbit u s k‖ ≤ 4 / ((k : ℝ) + 1) := by
  have horbit := finite_orbit_norm_bound_of_upper_bound u s R Z hR hu hZ k hs k (le_refl k)
  apply horbit.trans
  apply (div_le_div_iff₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)).mpr
  linarith

/-- Joint analyticity of `q` and `Γ` implies analyticity of their actual
finite-orbit residual; this property is not assumed for the orbit residual. -/
theorem differentiableOn_prepared_orbit (q Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u : ℂ) (R Z : ℝ) (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hq : DifferentiableOn ℂ q (preparationPolydisc Z))
    (hΓ : DifferentiableOn ℂ Γ (preparationPolydisc Z)) (k : ℕ) :
    DifferentiableOn ℂ (fun s => preparedResidual q Γ N s (orbit u s k))
      (closedBall 0 (parameterRadius Z k)) := by
  have hgraph : DifferentiableOn ℂ (fun s => (s, orbit u s k))
      (closedBall 0 (parameterRadius Z k)) :=
    (differentiable_id.prodMk (differentiable_orbit_parameter u k)).differentiableOn
  have hmaps : Set.MapsTo (fun s => (s, orbit u s k))
      (closedBall 0 (parameterRadius Z k)) (preparationPolydisc Z) := by
    intro s hs
    apply orbit_graph_mem_polydisc u s R Z hR hu hZ k
    simpa [mem_closedBall, dist_zero_right] using hs
  exact ((hq.pow N).mul hΓ).comp hgraph hmaps

/-- The preparation factor bound and the genuine finite-orbit bound give the
uniform Cauchy-circle residual bound with exponent `2N`. -/
theorem norm_prepared_orbit_le (q Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u s : ℂ) (R Z Cq M : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hCq : 0 ≤ Cq) (_hM : 0 ≤ M)
    (hqBound : ∀ p ∈ preparationPolydisc Z, ‖q p‖ ≤ ‖p.2‖ ^ 2 + Cq * ‖p.1‖)
    (hΓBound : ∀ p ∈ preparationPolydisc Z, ‖Γ p‖ ≤ M)
    (k : ℕ) (hs : ‖s‖ ≤ parameterRadius Z k) :
    ‖preparedResidual q Γ N s (orbit u s k)‖ ≤
      M * (16 + Cq * parameterRadius Z 0) ^ N / ((k : ℝ) + 1) ^ (2 * N) := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hc := parameterRadius_pos Z hZ0 0
  have hp := orbit_graph_mem_polydisc u s R Z hR hu hZ k hs
  have ho := finite_orbit_norm_le_four_div u s R Z hR hu hZ k hs
  have hqp : ‖q (s, orbit u s k)‖ ≤
      (16 + Cq * parameterRadius Z 0) / ((k : ℝ) + 1) ^ 2 := by
    apply (hqBound _ hp).trans
    calc
      ‖orbit u s k‖ ^ 2 + Cq * ‖s‖ ≤
          (4 / ((k : ℝ) + 1)) ^ 2 + Cq * parameterRadius Z k := by
        exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) ho 2)
          (mul_le_mul_of_nonneg_left hs hCq)
      _ = _ := by rw [parameterRadius_eq]; field_simp; ring
  have hQ : 0 ≤ (16 + Cq * parameterRadius Z 0) / ((k : ℝ) + 1) ^ 2 := by positivity
  rw [preparedResidual, norm_mul, norm_pow]
  calc
    _ ≤ ((16 + Cq * parameterRadius Z 0) / ((k : ℝ) + 1) ^ 2) ^ N * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hqp N) (hΓBound _ hp)
        (norm_nonneg _) (pow_nonneg hQ N)
    _ = _ := by rw [div_pow, ← pow_mul]; ring

/-- Genuine Cauchy differentiation of the actual orbit residual yields the
summable `k^(2-2N)` derivative decay without an orbit-velocity assumption. -/
theorem norm_deriv_prepared_orbit_le (q Γ : ℂ × ℂ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (u : ℂ) (R Z Cq M : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hCq : 0 ≤ Cq) (hM : 0 ≤ M)
    (hq : DifferentiableOn ℂ q (preparationPolydisc Z))
    (hΓ : DifferentiableOn ℂ Γ (preparationPolydisc Z))
    (hqBound : ∀ p ∈ preparationPolydisc Z, ‖q p‖ ≤ ‖p.2‖ ^ 2 + Cq * ‖p.1‖)
    (hΓBound : ∀ p ∈ preparationPolydisc Z, ‖Γ p‖ ≤ M) (k : ℕ) :
    ‖deriv (fun s => preparedResidual q Γ N s (orbit u s k)) 0‖ ≤
      (M * (16 + Cq * parameterRadius Z 0) ^ N / parameterRadius Z 0) /
        ((k : ℝ) + 1) ^ (2 * N - 2) := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hr := parameterRadius_pos Z hZ0 k
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ)) hr
    ((differentiableOn_prepared_orbit q Γ N u R Z hR hu hZ hq hΓ k).mono
      closure_ball_subset_closedBall).diffContOnCl
    (fun s hs => norm_prepared_orbit_le q Γ N u s R Z Cq M hR hu hZ hCq hM
      hqBound hΓBound k (by
        have hn : ‖s‖ = parameterRadius Z k := by
          simpa [mem_sphere, dist_zero_right] using hs
        exact hn.le))
  apply h.trans_eq
  rw [parameterRadius_eq Z k]
  have hexp : 2 * N = (2 * N - 2) + 2 := by omega
  have hpow : ((k : ℝ) + 1) ^ (2 * N) =
      ((k : ℝ) + 1) ^ (2 * N - 2) * ((k : ℝ) + 1) ^ 2 := by
    conv_lhs => rw [hexp, pow_add]
  rw [hpow]
  field_simp

/-- The derivative series of the actual prepared residual is absolutely
convergent once `N≥2`; neither term decay nor orbit velocity is assumed. -/
theorem summable_norm_deriv_prepared_orbit (q Γ : ℂ × ℂ → ℂ) (N : ℕ) (hN : 2 ≤ N)
    (u : ℂ) (R Z Cq M : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hCq : 0 ≤ Cq) (hM : 0 ≤ M)
    (hq : DifferentiableOn ℂ q (preparationPolydisc Z))
    (hΓ : DifferentiableOn ℂ Γ (preparationPolydisc Z))
    (hqBound : ∀ p ∈ preparationPolydisc Z, ‖q p‖ ≤ ‖p.2‖ ^ 2 + Cq * ‖p.1‖)
    (hΓBound : ∀ p ∈ preparationPolydisc Z, ‖Γ p‖ ≤ M) :
    Summable (fun k => ‖deriv (fun s => preparedResidual q Γ N s (orbit u s k)) 0‖) := by
  apply Kneser.summable_norm_of_parabolic_bound _
    (M * (16 + Cq * parameterRadius Z 0) ^ N / parameterRadius Z 0)
    (q := 2 * N - 2) (by omega)
  intro k
  exact norm_deriv_prepared_orbit_le q Γ N (by omega) u R Z Cq M hR hu hZ hCq hM
    hq hΓ hqBound hΓBound k

end Kneser.PreparedResidualEstimates

end
