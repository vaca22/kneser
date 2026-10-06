import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The head/tail step in one-sided differentiation

The analytic construction must supply its finite-head and infinite-tail bounds.
This file checks their assembly, and proves that an error of order `s^q`, `q > 1`,
really gives the right derivative. It does not assume that the infinite orbit
sum may be differentiated term by term.
-/

namespace Kneser

open Filter Set
open scoped Topology

/-- Exact assembly of the error estimate in the one-sided differentiation proof.
The scalar `s` is real; the coordinate and its derivative may be complex. -/
theorem head_tail_error_bound
    (s : ℝ) (ψs ψ0 dψ Hs H0 dH Ts T0 dT : ℂ)
    (eψ eH eT eD : ℝ)
    (hψ : ‖ψs - ψ0 - s • dψ‖ ≤ eψ)
    (hH : ‖Hs - H0 - s • dH‖ ≤ eH)
    (hTs : ‖Ts‖ ≤ eT) (hT0 : ‖T0‖ ≤ eT)
    (hD : ‖s • dT‖ ≤ eD) :
    ‖(ψs + Hs + Ts) - (ψ0 + H0 + T0) - s • (dψ + dH + dT)‖
      ≤ eψ + eH + 2 * eT + eD := by
  have heq : (ψs + Hs + Ts) - (ψ0 + H0 + T0) - s • (dψ + dH + dT) =
      (ψs - ψ0 - s • dψ) + (Hs - H0 - s • dH) + Ts - T0 - s • dT := by
    simp only [smul_add]
    abel
  rw [heq]
  have h1 := norm_sub_le ((ψs - ψ0 - s • dψ) + (Hs - H0 - s • dH) + Ts - T0)
    (s • dT)
  have h2 := norm_sub_le ((ψs - ψ0 - s • dψ) + (Hs - H0 - s • dH) + Ts) T0
  have h3 := norm_add_le ((ψs - ψ0 - s • dψ) + (Hs - H0 - s • dH)) Ts
  have h4 := norm_add_le (ψs - ψ0 - s • dψ) (Hs - H0 - s • dH)
  linarith

/-- A superlinear right-hand remainder proves a right derivative.
Only a norm bound on the actual remainder is needed; `q = 10/9` is allowed. -/
theorem hasDerivWithinAt_of_power_error
    (A : ℝ → ℂ) (d : ℂ) (C q : ℝ) (hq : 1 < q)
    (hbound : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ‖A s - A 0 - s • d‖ ≤ C * s ^ q) :
    HasDerivWithinAt A d (Ici 0) 0 := by
  have hp : 0 < q - 1 := sub_pos.mpr hq
  have hlim : Tendsto (fun s : ℝ => C * s ^ (q - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hpow := (Real.continuousAt_rpow_const (0 : ℝ) (q - 1) (Or.inr hp.le)).tendsto
    have hzero : (0 : ℝ) ^ (q - 1) = 0 := Real.zero_rpow hp.ne'
    simpa only [hzero, mul_zero] using
      (tendsto_const_nhds.mul (hpow.mono_left nhdsWithin_le_nhds))
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hupper : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖s‖⁻¹ * ‖A s - A 0 - s • d‖ ≤ C * s ^ (q - 1) := by
    filter_upwards [hbound, hpos] with s hs hspos
    have h := mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hspos.le)
    simpa only [Real.norm_eq_abs, abs_of_pos hspos, Real.rpow_sub hspos,
      Real.rpow_one, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hnonneg : ∀ s : ℝ, 0 ≤ ‖s‖⁻¹ * ‖A s - A 0 - s • d‖ :=
    fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg s)) (norm_nonneg _)
  have ht := squeeze_zero' (Eventually.of_forall hnonneg) hupper hlim
  apply HasDerivWithinAt.Ici_of_Ioi
  apply hasDerivWithinAt_iff_tendsto.mpr
  simpa only [sub_zero] using ht

end Kneser
