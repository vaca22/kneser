import Kneser.ReflectedHigherModelTime
import Kneser.ReflectedPreparedFirstOrder
import Kneser.UniformActualHigherCoordinate

/-! All-order estimates for the genuine reflected inverse orbit series.
The finite complex orbit discs, positive-real infinite tails, reflected
logarithmic model and polynomial correction are derived from the actual
exponential preparation.  The residual is evaluated at the inverse image,
so the series correctly starts at inverse iterate one. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.ReflectedHigherPreparedCoordinate

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.ReflectedEvenOrbitDiscs
open Kneser.ExponentialPreparedHigher Kneser.HigherOrderCutoff Kneser.AsymptoticBalance
open Kneser.UniformHigherOrderCutoff Kneser.FirstOrderCutoff
open scoped Topology BigOperators

def shiftedTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (v s : ℂ) (k : ℕ) : ℂ :=
  descendedTerm A B Γ N v s (k + 1)

theorem shifted_disc_bounds (term : ℂ → ℕ → ℂ) (c M : ℝ) (N : ℕ)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun z => term z k) (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term z k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) :
    (∀ k, DiffContOnCl ℂ (fun z => term z (k + 1))
      (ball 0 ((c / 4) / ((k : ℝ) + 1) ^ 2))) ∧
    (∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ (c / 4) / ((k : ℝ) + 1) ^ 2 →
      ‖term z (k + 1)‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) := by
  constructor
  · intro k
    apply (hdisc (k + 1)).mono
    apply Metric.ball_subset_ball
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      ReflectedPreparedFirstOrder.disc_radius_shift_bound c hc.le k
  · intro k z hz
    have ht := hbound (k + 1) z (hz.trans (by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
        ReflectedPreparedFirstOrder.disc_radius_shift_bound c hc.le k))
    apply ht.trans
    apply div_le_div_of_nonneg_left hM (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) (2 * N)

def preparedSeries (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ) (s : ℝ) : ℂ :=
  coordinateSeries (fun s : ℝ => ReflectedHigherModelTime.modelTime U H n e s v)
    (fun s : ℝ => shiftedTerm A B Γ (n + 1) v s) s

def preparedCoefficient (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (v : ℂ) (j : ℕ) : ℂ :=
  coordinateCoefficient (fun s => ReflectedHigherModelTime.modelTime U H n e s v)
    (shiftedTerm A B Γ (n + 1) v) j

theorem prepared_compact_higher_expansion
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ)
    (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0) (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hΓ : AnalyticAt ℂ Γ 0) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) 0) (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (m : ℕ) (hm : 1 ≤ m) (hN : m * m + m + 1 ≤ n + 1) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ S : Set ℂ, IsCompact S →
      (∀ v ∈ S, R₀ + 1 ≤ (inverseCoordinate v).re) →
      (∀ v ∈ S, ∀ j ≤ m, Summable (fun k =>
        ‖termCoefficient (shiftedTerm A B Γ (n + 1) v) j k‖)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S,
        ‖preparedSeries U H n e A B Γ v s -
          ∑ j ∈ Finset.range (m + 1), (s : ℂ) ^ j *
            preparedCoefficient U H n e A B Γ v j‖ ≤
          C * s ^ ((m : ℝ) + gamma m (n + 1)) := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := exists_uniform_prepared_orbit_disc_bounds A B Γ (n + 1)
    hA hB hA0 hB0 hΓ hEven
  obtain ⟨R₂, CT, hR₂, hCT, hreal⟩ :=
    ReflectedPreparedRealMajorant.exists_actual_prepared_real_majorant A B K
      (descendedFactor Γ) (n + 1) hK hK0 hfactor
      (continuousAt_descendedFactor Γ hΓ.continuousAt)
  let R₀ : ℝ := max R₁ R₂
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro S hS hpetal
  have hune : ∀ v ∈ S, v ≠ 0 := by
    intro v hv heq
    have hh := hpetal v hv
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at hh
    linarith
  have hi : ContinuousOn inverseCoordinate S := by
    intro v hv
    exact (continuousAt_const.div continuousAt_id (hune v hv)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hS.exists_bound_of_continuousOn hi
  let Z : ℝ := max Z₁ 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hZv : ∀ v ∈ S, ‖inverseCoordinate v‖ ≤ Z :=
    fun v hv => (hZ₁ v hv).trans (le_max_left _ _)
  have hneg : ∀ v ∈ S, v.re < 0 := by
    intro v hv
    have hh := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
      (show 0 < (inverseCoordinate v).re by linarith [hpetal v hv])
    simpa only [Complex.neg_re, neg_pos] using hh
  obtain ⟨r, Mψ, hr, hMψ, hmodel⟩ :=
    ReflectedHigherModelTime.exists_compact_disc_bounds n e hU hU0 hH hHne he S hS hneg
  obtain ⟨c, M, hc, hM, hcommon⟩ := hdiscs R₀ (le_max_left _ _) Z hZ
  have hcommonS : ∀ v ∈ S,
      (∀ k, DiffContOnCl ℂ (fun s => shiftedTerm A B Γ (n + 1) v s k)
        (ball 0 ((c / 4) / ((k : ℝ) + 1) ^ 2))) ∧
      (∀ (k : ℕ) (s : ℂ), ‖s‖ ≤ (c / 4) / ((k : ℝ) + 1) ^ 2 →
        ‖shiftedTerm A B Γ (n + 1) v s k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * (n + 1))) := by
    intro v hv
    obtain ⟨hd, hb⟩ := hcommon v (by linarith [hpetal v hv]) (hZv v hv)
    exact shifted_disc_bounds (descendedTerm A B Γ (n + 1) v) c M (n + 1) hc hM hd hb
  obtain ⟨s₀, hs₀, hterms⟩ := hreal R₀ (le_max_right _ _) Z hZ
  have htermS : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ v ∈ S, ∀ k,
      ‖shiftedTerm A B Γ (n + 1) v (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ (2 * (n + 1)) := by
    have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
      (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hss v hv k
    have ht := hterms s hs hss v (hpetal v hv) (hZv v hv) (k + 1)
    change ‖descendedTerm A B Γ (n + 1) v (s : ℂ) (k + 1)‖ ≤ _
    rw [descendedTerm_eq]
    apply ht.trans
    apply div_le_div_of_nonneg_left hCT (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by push_cast; linarith) (2 * (n + 1))
  exact coordinate_expansion_uniform_from_bounds S
    (fun v s => ReflectedHigherModelTime.modelTime U H n e s v)
    (fun v => shiftedTerm A B Γ (n + 1) v) m (n + 1) r Mψ (c / 4) M CT
    hm hN hr hMψ (by positivity) hM hCT (fun v hv => (hmodel v hv).1)
    (fun v hv z hz => (hmodel v hv).2 z (mem_closedBall.mpr (mem_sphere.mp hz).le))
    (fun v hv => (hcommonS v hv).1) (fun v hv => (hcommonS v hv).2) htermS

end Kneser.ReflectedHigherPreparedCoordinate

end
