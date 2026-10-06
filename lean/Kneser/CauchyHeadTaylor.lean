import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# A genuine Cauchy estimate for the finite head

The Taylor remainder is obtained by subtracting the Cauchy kernels for the
value, constant term, and first derivative. It is not supplied as a hypothesis.
The explicit estimate applies to any finite head holomorphic on a disc whose
radius is proportional to `J⁻²`.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.CauchyHeadTaylor

open Complex MeasureTheory Metric
open scoped Topology

/-- Exact Cauchy-integral representation of the first Taylor remainder. -/
theorem cauchy_first_remainder (f : ℂ → ℂ) (R : ℝ) (s : ℂ)
    (hR : 0 < R) (hf : DiffContOnCl ℂ f (ball 0 R)) (hs : ‖s‖ < R) :
    (2 * (Real.pi : ℂ) * Complex.I) * (f s - f 0 - s * deriv f 0) =
      ∮ z in C((0 : ℂ), R), f z * s ^ 2 / (z ^ 2 * (z - s)) := by
  have hsball : s ∈ ball (0 : ℂ) R := by simpa [mem_ball, dist_zero_right] using hs
  have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) R := by simpa [mem_ball] using hR
  have hfc : ContinuousOn f (sphere (0 : ℂ) R) :=
    hf.continuousOn_ball.mono sphere_subset_closedBall
  have hzero : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := by
    intro z hz heq
    subst z
    exact hR.ne (by simpa [mem_sphere] using hz)
  have hzs : ∀ z ∈ sphere (0 : ℂ) R, z - s ≠ 0 := by
    intro z hz heq
    have hzR : ‖z‖ = R := by simpa [mem_sphere, dist_zero_right] using hz
    have hzEq : z = s := sub_eq_zero.mp heq
    rw [hzEq] at hzR
    exact (ne_of_lt hs) hzR
  have hks : CircleIntegrable (fun z => f z / (z - s)) 0 R :=
    (hfc.div (continuousOn_id.sub continuousOn_const) hzs).circleIntegrable hR.le
  have hk0 : CircleIntegrable (fun z => f z / z) 0 R :=
    (hfc.div continuousOn_id hzero).circleIntegrable hR.le
  have hk2 : CircleIntegrable (fun z => f z / z ^ 2) 0 R :=
    (hfc.div (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (hzero z hz))).circleIntegrable hR.le
  have hks2 : CircleIntegrable (fun z => s * (f z / z ^ 2)) 0 R := by
    exact (continuousOn_const.mul (hfc.div (continuousOn_id.pow 2)
      (fun z hz => pow_ne_zero 2 (hzero z hz)))).circleIntegrable hR.le
  have hval : (∮ z in C((0 : ℂ), R), f z / (z - s)) =
      (2 * (Real.pi : ℂ) * Complex.I) * f s := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hf.circleIntegral_sub_inv_smul hsball
  have hconst : (∮ z in C((0 : ℂ), R), f z / z) =
      (2 * (Real.pi : ℂ) * Complex.I) * f 0 := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hf.circleIntegral_sub_inv_smul h0ball
  have hderiv : (∮ z in C((0 : ℂ), R), f z / z ^ 2) =
      (2 * (Real.pi : ℂ) * Complex.I) * deriv f 0 := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hf.deriv_eq_smul_circleIntegral hR
  have heq : (∮ z in C((0 : ℂ), R), f z * s ^ 2 / (z ^ 2 * (z - s))) =
      ∮ z in C((0 : ℂ), R), (f z / (z - s) - f z / z) - s * (f z / z ^ 2) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    field_simp [hzero z hz, hzs z hz]
    ring
  have hsub := circleIntegral.integral_sub (hks.sub hk0) hks2
  have hsub0 := circleIntegral.integral_sub hks hk0
  simp only [Pi.sub_apply] at hsub hsub0
  rw [heq, hsub, hsub0, circleIntegral.integral_const_mul, hval, hconst, hderiv]
  ring

/-- Cauchy's estimate yields a second-order remainder from analyticity and a
uniform boundary bound alone. -/
theorem norm_first_remainder_le (f : ℂ → ℂ) (R M : ℝ) (s : ℂ)
    (hR : 0 < R) (hM : 0 ≤ M) (hf : DiffContOnCl ℂ f (ball 0 R))
    (hbound : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (hs : ‖s‖ ≤ R / 2) :
    ‖f s - f 0 - s * deriv f 0‖ ≤ 2 * M * ‖s‖ ^ 2 / R ^ 2 := by
  have hslt : ‖s‖ < R := by linarith
  have hcircle := circleIntegral.norm_integral_le_of_norm_le_const (hR.le)
    (f := fun z => f z * s ^ 2 / (z ^ 2 * (z - s)))
    (c := (0 : ℂ)) (C := 2 * M * ‖s‖ ^ 2 / R ^ 3) (by
      intro z hz
      have hzR : ‖z‖ = R := by simpa [mem_sphere, dist_zero_right] using hz
      have hlower : R / 2 ≤ ‖z - s‖ := by
        have h := norm_sub_norm_le z s
        rw [hzR] at h
        linarith
      rw [norm_div, norm_mul, norm_mul, norm_pow, norm_pow, hzR]
      calc
        ‖f z‖ * ‖s‖ ^ 2 / (R ^ 2 * ‖z - s‖) ≤
            M * ‖s‖ ^ 2 / (R ^ 2 * (R / 2)) := by
          gcongr
          exact hbound z hz
        _ = _ := by field_simp)
  have hnorm := congrArg norm (cauchy_first_remainder f R s hR hf hslt)
  have hC : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    simp [Real.pi_pos.le]
  rw [norm_mul, hC] at hnorm
  rw [← hnorm] at hcircle
  have hfinal : (2 * Real.pi) * ‖f s - f 0 - s * deriv f 0‖ ≤
      (2 * Real.pi) * (2 * M * ‖s‖ ^ 2 / R ^ 2) := by
    convert hcircle using 1
    field_simp
  exact (mul_le_mul_iff_right₀ Real.two_pi_pos).mp hfinal

/-- On a disc of radius `c/J²`, the finite-head remainder is `O(s²J⁴)`.
The estimate is deduced from Cauchy's formula, not assumed. -/
theorem finite_head_remainder_le (H : ℕ → ℂ → ℂ) (c M : ℝ) (J : ℕ) (s : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (hJ : 0 < J)
    (hH : DiffContOnCl ℂ (H J) (ball 0 (c / (J : ℝ) ^ 2)))
    (hbound : ∀ z ∈ sphere (0 : ℂ) (c / (J : ℝ) ^ 2), ‖H J z‖ ≤ M)
    (hs : |s| ≤ c / (2 * (J : ℝ) ^ 2)) :
    ‖H J (s : ℂ) - H J 0 - (s : ℂ) * deriv (H J) 0‖ ≤
      (2 * M / c ^ 2) * s ^ 2 * (J : ℝ) ^ 4 := by
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hR : 0 < c / (J : ℝ) ^ 2 := div_pos hc (sq_pos_of_pos hJR)
  have hs' : ‖(s : ℂ)‖ ≤ (c / (J : ℝ) ^ 2) / 2 := by
    simpa [Complex.norm_real, Real.norm_eq_abs, div_div, mul_comm] using hs
  have h := norm_first_remainder_le (H J) (c / (J : ℝ) ^ 2) M (s : ℂ)
    hR hM hH hbound hs'
  convert h using 1
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  field_simp

/-- Cauchy's estimate also gives every actual derivative of the finite head,
with the explicit scaling `J^(2j)` of the shrinking parameter disc. -/
theorem finite_head_higher_derivative_le (H : ℕ → ℂ → ℂ) (c M : ℝ)
    (J j : ℕ) (hc : 0 < c) (hJ : 0 < J)
    (hH : DiffContOnCl ℂ (H J) (ball 0 (c / (J : ℝ) ^ 2)))
    (hbound : ∀ z ∈ sphere (0 : ℂ) (c / (J : ℝ) ^ 2), ‖H J z‖ ≤ M) :
    ‖iteratedDeriv j (H J) 0‖ ≤
      ((j.factorial : ℝ) * M / c ^ j) * (J : ℝ) ^ (2 * j) := by
  have hJR : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hr : 0 < c / (J : ℝ) ^ 2 := by positivity
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr hH hbound
  convert h using 1
  rw [div_pow, ← pow_mul]
  field_simp

end Kneser.CauchyHeadTaylor

end
