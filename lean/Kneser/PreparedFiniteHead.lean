import Kneser.PreparedResidualEstimates
import Kneser.FirstOrderCutoff

/-!
# Finite heads of the actual prepared exponential orbit

Joint analyticity and bounds of the preparation factors imply the analytic
disc estimate for every finite orbit sum. The moving-cutoff expansion then
uses these conclusions directly, rather than assuming a head estimate.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.PreparedFiniteHead

open Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.PerturbedExponentialOrbit Kneser.PreparedResidualEstimates
open Kneser.FirstOrderCutoff Kneser.PowerSeriesTail
open Complex Metric Filter Set
open scoped Topology BigOperators

/-- Residuals evaluated on the actual finite exponential orbit. -/
def preparedTerm (q Γ : ℂ × ℂ → ℂ) (N : ℕ) (u : ℂ) (s : ℂ) (k : ℕ) : ℂ :=
  preparedResidual q Γ N s (orbit u s k)

/-- All terms in a head of length `J` admit the common parameter disc. -/
theorem headRadius_le_parameterRadius (Z : ℝ) (hZ : 0 ≤ Z)
    (J : ℕ) (_hJ : 0 < J) (k : ℕ) (hk : k < J) :
    parameterRadius Z 0 / (J : ℝ) ^ 2 ≤ parameterRadius Z k := by
  have hkJ : (k : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
  have hpow : ((k : ℝ) + 1) ^ 2 ≤ (J : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hkJ 2
  rw [parameterRadius_eq Z k]
  exact div_le_div_of_nonneg_left (parameterRadius_pos Z hZ 0).le (by positivity) hpow

/-- The genuine finite sum is holomorphic on its common disc and continuous
up to the boundary; no analytic-head hypothesis is used. -/
theorem diffContOnCl_prepared_head (q Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u : ℂ) (R Z : ℝ) (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hq : DifferentiableOn ℂ q (preparationPolydisc Z))
    (hΓ : DifferentiableOn ℂ Γ (preparationPolydisc Z))
    (J : ℕ) (hJ : 0 < J) :
    DiffContOnCl ℂ (finiteHead (preparedTerm q Γ N u) J)
      (ball 0 (parameterRadius Z 0 / (J : ℝ) ^ 2)) := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hd : DifferentiableOn ℂ (finiteHead (preparedTerm q Γ N u) J)
      (closedBall 0 (parameterRadius Z 0 / (J : ℝ) ^ 2)) := by
    apply DifferentiableOn.fun_sum
    intro k hk
    exact (differentiableOn_prepared_orbit q Γ N u R Z hR hu hZ hq hΓ k).mono
      (closedBall_subset_closedBall
        (headRadius_le_parameterRadius Z hZ0 J hJ k (Finset.mem_range.mp hk)))
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl

/-- The norm of every finite head is bounded by the actual power-majorant
sum. Its constant is independent of the head length. -/
theorem norm_prepared_head_le (q Γ : ℂ × ℂ → ℂ) (N : ℕ) (hN : 1 ≤ N)
    (u : ℂ) (R Z Cq M : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hCq : 0 ≤ Cq) (hM : 0 ≤ M)
    (hqBound : ∀ p ∈ preparationPolydisc Z, ‖q p‖ ≤ ‖p.2‖ ^ 2 + Cq * ‖p.1‖)
    (hΓBound : ∀ p ∈ preparationPolydisc Z, ‖Γ p‖ ≤ M)
    (J : ℕ) (hJ : 0 < J) (s : ℂ)
    (hs : ‖s‖ ≤ parameterRadius Z 0 / (J : ℝ) ^ 2) :
    ‖finiteHead (preparedTerm q Γ N u) J s‖ ≤
      (M * (16 + Cq * parameterRadius Z 0) ^ N) * powerConstant (2 * N) := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hc := parameterRadius_pos Z hZ0 0
  let C := M * (16 + Cq * parameterRadius Z 0) ^ N
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsum := summable_parabolic_majorant C (show 2 ≤ 2 * N by omega)
  calc
    ‖finiteHead (preparedTerm q Γ N u) J s‖ ≤
        ∑ k ∈ Finset.range J, ‖preparedTerm q Γ N u s k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range J, C / ((k : ℝ) + 1) ^ (2 * N) := by
      apply Finset.sum_le_sum
      intro k hk
      exact norm_prepared_orbit_le q Γ N u s R Z Cq M hR hu hZ hCq hM hqBound hΓBound k
        (hs.trans (headRadius_le_parameterRadius Z hZ0 J hJ k (Finset.mem_range.mp hk)))
    _ ≤ ∑' k : ℕ, C / ((k : ℝ) + 1) ^ (2 * N) :=
      hsum.sum_le_tsum _ (fun _ _ => by positivity)
    _ = C * powerConstant (2 * N) := by
      rw [show (fun k : ℕ => C / ((k : ℝ) + 1) ^ (2 * N)) =
        fun k : ℕ => C * (1 / ((k : ℝ) + 1) ^ (2 * N)) by funext k; ring,
        tsum_mul_left]
      rfl

/-- The actual finite-orbit terms have their actual complex derivatives.
The derivative is obtained from preparation analyticity and the proved orbit. -/
theorem hasDerivAt_preparedTerm (q Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u : ℂ) (R Z : ℝ) (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hq : DifferentiableOn ℂ q (preparationPolydisc Z))
    (hΓ : DifferentiableOn ℂ Γ (preparationPolydisc Z)) (k : ℕ) :
    HasDerivAt (fun s => preparedTerm q Γ N u s k)
      (deriv (fun s => preparedTerm q Γ N u s k) 0) 0 := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  exact ((differentiableOn_prepared_orbit q Γ N u R Z hR hu hZ hq hΓ k).differentiableAt
    (closedBall_mem_nhds 0 (parameterRadius_pos Z hZ0 k))).hasDerivAt

/-- Applying the moving-cutoff theorem to the actual prepared family removes
all finite-head analyticity, head-bound, derivative and derivative-bound inputs.
Only the preparation data and an infinite real-orbit term bound remain. -/
theorem prepared_coordinate_expansion
    (ψ : ℂ → ℂ) (q Γ : ℂ × ℂ → ℂ) (u : ℂ)
    (R Z Cq M r Mψ CT : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hCq : 0 ≤ Cq) (hM : 0 ≤ M) (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hCT : 0 ≤ CT)
    (hq : DifferentiableOn ℂ q (preparationPolydisc Z))
    (hΓ : DifferentiableOn ℂ Γ (preparationPolydisc Z))
    (hqBound : ∀ p ∈ preparationPolydisc Z, ‖q p‖ ≤ ‖p.2‖ ^ 2 + Cq * ‖p.1‖)
    (hΓBound : ∀ p ∈ preparationPolydisc Z, ‖Γ p‖ ≤ M)
    (hψ : DiffContOnCl ℂ ψ (ball 0 r))
    (hψbound : ∀ z ∈ sphere (0 : ℂ) r, ‖ψ z‖ ≤ Mψ)
    (hterms : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖preparedTerm q Γ 3 u (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 6) :
    let term := preparedTerm q Γ 3 u
    let δ := fun k => deriv (fun s => term s k) 0
    let A := coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ))
    let d := firstOrderCoefficient (deriv ψ 0) δ
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ‖A s - A 0 - s • d‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
      HasDerivWithinAt A d (Ici 0) 0 := by
  dsimp only
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  let c := parameterRadius Z 0
  have hc : 0 < c := parameterRadius_pos Z hZ0 0
  let C0 := M * (16 + Cq * c) ^ 3
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hδ := hasDerivAt_preparedTerm q Γ 3 u R Z hR hu hZ hq hΓ
  have hzero : ∀ k, ‖preparedTerm q Γ 3 u 0 k‖ ≤
      (C0 + CT) / ((k : ℝ) + 1) ^ 6 := by
    intro k
    have ht := norm_prepared_orbit_le q Γ 3 u 0 R Z Cq M hR hu hZ hCq hM
      hqBound hΓBound k (by simpa using (parameterRadius_pos Z hZ0 k).le)
    apply ht.trans
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right hCT) (by positivity)
  have hterms' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖preparedTerm q Γ 3 u (s : ℂ) k‖ ≤ (C0 + CT) / ((k : ℝ) + 1) ^ 6 := by
    filter_upwards [hterms] with s hs
    intro k
    exact (hs k).trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left hC0) (by positivity))
  have hδbound : ∀ k, ‖deriv (fun s => preparedTerm q Γ 3 u s k) 0‖ ≤
      (C0 / c) / ((k : ℝ) + 1) ^ 4 := by
    intro k
    exact norm_deriv_prepared_orbit_le q Γ 3 (by norm_num) u R Z Cq M hR hu hZ
      hCq hM hq hΓ hqBound hΓBound k
  have h := coordinate_expansion_from_disc_and_term_bounds ψ (preparedTerm q Γ 3 u)
    (fun k => deriv (fun s => preparedTerm q Γ 3 u s k) 0)
    r Mψ c (C0 * powerConstant 6) (C0 + CT) (C0 / c) hr hMψ hc
    (mul_nonneg hC0 (powerConstant_nonneg 6)) (add_nonneg hC0 hCT) (by positivity)
    hψ hψbound (diffContOnCl_prepared_head q Γ 3 u R Z hR hu hZ hq hΓ)
    (by
      intro J hJ s hs
      exact norm_prepared_head_le q Γ 3 (by norm_num) u R Z Cq M hR hu hZ hCq hM
        hqBound hΓBound J hJ s (by
          have hn : ‖s‖ = c / (J : ℝ) ^ 2 := by
            simpa [mem_sphere, dist_zero_right] using hs
          exact hn.le))
    hδ hzero hterms' hδbound
  refine ⟨_, ?_, h.1, h.2⟩
  have hpc4 := powerConstant_nonneg 4
  have hpc6 := powerConstant_nonneg 6
  positivity

end Kneser.PreparedFiniteHead

end
