import Kneser.HornCoefficient
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Differentiation of the actual gate Fourier coefficients

The Fourier operator is the Bochner interval integral on the horizontal gate
`[0,1] + iY`. Its first coefficient is derived from a uniform one-sided
expansion of the gate transition map; the derivatives of the Fourier
coefficients are conclusions, not additional hypotheses.

The remaining input is the uniform expansion of the actual transition map
and integrability on the gate. This module does not assert those dynamical
estimates for an unspecified transition map.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.GateFourierDerivative

open MeasureTheory Filter
open scoped Topology Interval

/-- Parameterization of the horizontal integration gate. -/
def gatePoint (Y x : ℝ) : ℂ := (x : ℂ) + Complex.I * (Y : ℂ)

/-- The Fourier weight on the gate. -/
def gateWeight (n : ℤ) (Y x : ℝ) : ℂ :=
  Complex.exp (-Kneser.fourierFrequency n * gatePoint Y x)

/-- The actual gate Fourier coefficient of `T-id`. -/
def gateFourierCoefficient (n : ℤ) (Y : ℝ) (T : ℂ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, (T (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x

/-- The correction coefficient is the actual integral of the gate correction. -/
def gateCorrectionCoefficient (n : ℤ) (Y : ℝ) (D : ℂ → ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1, D (gatePoint Y x) * gateWeight n Y x

/-- The Fourier weight has constant norm on the horizontal gate. -/
theorem norm_gateWeight (n : ℤ) (Y x : ℝ) :
    ‖gateWeight n Y x‖ = Real.exp (2 * Real.pi * (n : ℝ) * Y) := by
  rw [gateWeight, Complex.norm_exp]
  congr 1
  simp [Kneser.fourierFrequency, gatePoint, Complex.mul_re, Complex.mul_im]

/-- Linearity of the actual integral identifies the coefficient remainder
with the weighted integral of the transition-map remainder. -/
theorem coefficient_remainder_eq_integral (n : ℤ) (Y s : ℝ)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (hTs : IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hT0 : IntervalIntegrable
      (fun x => (T 0 (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hD : IntervalIntegrable
      (fun x => D (gatePoint Y x) * gateWeight n Y x) volume 0 1) :
    gateFourierCoefficient n Y (T s) - gateFourierCoefficient n Y (T 0) -
      (s : ℂ) * gateCorrectionCoefficient n Y D =
      ∫ x in (0 : ℝ)..1,
        (T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)) *
          gateWeight n Y x := by
  have hpoint : (fun x =>
      (T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)) *
        gateWeight n Y x) =
      (fun x => ((T s (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x -
        (T 0 (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x) -
        (s : ℂ) * (D (gatePoint Y x) * gateWeight n Y x)) := by
    funext x
    ring
  rw [hpoint, intervalIntegral.integral_sub (hTs.sub hT0) (hD.const_mul (s : ℂ)),
    intervalIntegral.integral_sub hTs hT0, intervalIntegral.integral_const_mul]
  rfl

/-- A uniform remainder on the gate gives the same order of remainder for
its actual Fourier integral, with the explicit gate-weight constant. -/
theorem norm_coefficient_remainder_le (n : ℤ) (Y s ε : ℝ)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (hTs : IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hT0 : IntervalIntegrable
      (fun x => (T 0 (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hD : IntervalIntegrable
      (fun x => D (gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hrem : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)‖ ≤
        |s| * ε) :
    ‖gateFourierCoefficient n Y (T s) - gateFourierCoefficient n Y (T 0) -
      (s : ℂ) * gateCorrectionCoefficient n Y D‖ ≤
      (|s| * ε) * Real.exp (2 * Real.pi * (n : ℝ) * Y) := by
  rw [coefficient_remainder_eq_integral n Y s T D hTs hT0 hD]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (C := (|s| * ε) * Real.exp (2 * Real.pi * (n : ℝ) * Y))
    (f := fun x =>
      (T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)) *
        gateWeight n Y x) (by
      intro x hx
      rw [norm_mul, norm_gateWeight]
      apply mul_le_mul_of_nonneg_right (hrem x ?_) (Real.exp_pos _).le
      have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
        simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact Set.Ioc_subset_Icc_self hx')
  simpa using h

/-- Uniform right-differentiability of the transition map implies actual
right-differentiability of each gate Fourier coefficient. -/
theorem hasDerivWithinAt_gateFourierCoefficient (n : ℤ) (Y : ℝ)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (ε : ℝ → ℝ)
    (hInt : ∀ s, IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hD : IntervalIntegrable
      (fun x => D (gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hUniform : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)‖ ≤
        |s| * ε s) :
    HasDerivWithinAt (fun s => gateFourierCoefficient n Y (T s))
      (gateCorrectionCoefficient n Y D) (Set.Ici 0) 0 := by
  apply HasDerivWithinAt.Ici_of_Ioi
  rw [hasDerivWithinAt_iff_tendsto]
  apply squeeze_zero' (g := fun s => ε s * Real.exp (2 * Real.pi * (n : ℝ) * Y))
  · exact Eventually.of_forall (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
      (norm_nonneg _))
  · filter_upwards [hUniform, self_mem_nhdsWithin] with s hs hpos
    have hsp : 0 < s := hpos
    have habs : 0 < |s| := abs_pos.mpr hsp.ne'
    have hbound := norm_coefficient_remainder_le n Y s (ε s) T D
      (hInt s) (hInt 0) hD hs
    simp only [sub_zero, Complex.real_smul] at *
    rw [Real.norm_eq_abs]
    calc
      |s|⁻¹ * ‖gateFourierCoefficient n Y (T s) - gateFourierCoefficient n Y (T 0) -
          (s : ℂ) * gateCorrectionCoefficient n Y D‖ ≤
          |s|⁻¹ * ((|s| * ε s) * Real.exp (2 * Real.pi * (n : ℝ) * Y)) :=
        mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr habs.le)
      _ = ε s * Real.exp (2 * Real.pi * (n : ℝ) * Y) := by
        field_simp
  · simpa using hε.mul_const (Real.exp (2 * Real.pi * (n : ℝ) * Y))

/-- End-to-end coefficient extraction from the actual gate transition map:
no Fourier-coefficient derivative is an input to this theorem. -/
theorem hasDerivWithinAt_log_normalized_gateFourier (n : ℤ) (Y : ℝ)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (ε : ℝ → ℝ) (B a : ℂ)
    (hInt : ∀ m s, IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hD : ∀ m, IntervalIntegrable
      (fun x => D (gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hUniform : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)‖ ≤
        |s| * ε s)
    (hn0 : gateFourierCoefficient n Y (T 0) = B)
    (h00 : gateFourierCoefficient 0 Y (T 0) = -a) (hB : B ≠ 0) :
    HasDerivWithinAt
      (fun s => Complex.log (Kneser.realNormalizedHornCoefficient n
        (fun t => gateFourierCoefficient n Y (T t))
        (fun t => gateFourierCoefficient 0 Y (T t)) s))
      (2 * Kneser.hornKappa n B (gateCorrectionCoefficient n Y D)
        (gateCorrectionCoefficient 0 Y D)) (Set.Ici 0) 0 := by
  apply Kneser.hasDerivWithinAt_log_realNormalizedHornCoefficient_right n
    (fun t => gateFourierCoefficient n Y (T t))
    (fun t => gateFourierCoefficient 0 Y (T t)) B a
    (gateCorrectionCoefficient n Y D) (gateCorrectionCoefficient 0 Y D)
    hn0 h00 hB
  · exact hasDerivWithinAt_gateFourierCoefficient n Y T D ε (hInt n) (hD n) hε hUniform
  · exact hasDerivWithinAt_gateFourierCoefficient 0 Y T D ε (hInt 0) (hD 0) hε hUniform

/-- The parameter conversion `dp/ds=2` gives the paper's explicit coefficient
from actual gate integrals and the uniform transition-map expansion. -/
theorem rightDeriv_log_gateFourier_div_parameter_eq (n : ℤ) (Y : ℝ)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (ε pOfS : ℝ → ℝ) (B a : ℂ)
    (hInt : ∀ m s, IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hD : ∀ m, IntervalIntegrable
      (fun x => D (gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hε : Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (hUniform : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0), ∀ x ∈ Set.Icc (0 : ℝ) 1,
      ‖T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)‖ ≤
        |s| * ε s)
    (hn0 : gateFourierCoefficient n Y (T 0) = B)
    (h00 : gateFourierCoefficient 0 Y (T 0) = -a) (hB : B ≠ 0)
    (hp : HasDerivWithinAt pOfS 2 (Set.Ici 0) 0) :
    derivWithin
      (fun s => Complex.log (Kneser.realNormalizedHornCoefficient n
        (fun t => gateFourierCoefficient n Y (T t))
        (fun t => gateFourierCoefficient 0 Y (T t)) s)) (Set.Ici 0) 0 /
      ((derivWithin pOfS (Set.Ici 0) 0 : ℝ) : ℂ) =
      Kneser.hornKappa n B (gateCorrectionCoefficient n Y D)
        (gateCorrectionCoefficient 0 Y D) := by
  rw [(hasDerivWithinAt_log_normalized_gateFourier n Y T D ε B a
    hInt hD hε hUniform hn0 h00 hB).derivWithin (uniqueDiffWithinAt_Ici 0),
    hp.derivWithin (uniqueDiffWithinAt_Ici 0)]
  norm_num

end Kneser.GateFourierDerivative

end
