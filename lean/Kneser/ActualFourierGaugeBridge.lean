import Kneser.FourierCenterShift
import Kneser.GrowingStripFourier

/-!
Exact transport of the actual Fourier integrals from a local gate to a
holomorphic periodic transition on a genuine strip.  The complex shift is
allowed to depend on the parameter: it cancels exactly in every nonzero
normalized horn coefficient, without a smallness or asymptotic estimate.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualFourierGaugeBridge

open Set Complex MeasureTheory Kneser.GateFourierDerivative
open Kneser.GateFourierHeight Kneser.FourierCenterShift
open Kneser.GrowingStripFourier
open scoped Topology Interval

/-- Equality only on the actual integration segment suffices. -/
theorem coefficient_eq_of_eq_on_real_gate (n : ℤ) (T S : ℂ → ℂ)
    (he : ∀ x ∈ Icc (0 : ℝ) 1, T (x : ℂ) = S (x : ℂ)) :
    gateFourierCoefficient n 0 T = gateFourierCoefficient n 0 S := by
  unfold gateFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  simp only [gatePoint, Complex.ofReal_zero, mul_zero, add_zero]
  rw [he x hx']

/-- Moving the gate of the centered extension uses holomorphy only on the
rectangle between the two genuine horizontal lines. -/
theorem centered_extension_height_eq_zero (n : ℤ) (T : ℂ → ℂ) (D : ℝ)
    (c : ℂ) (hD : 0 < D)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z + 1) = T z + 1)
    (hc : |c.im| < D) :
    gateFourierCoefficient n c.im (centered (stripExtension T D) c) =
      gateFourierCoefficient n 0 (centered (stripExtension T D) c) := by
  apply gateFourier_height_independent n _ c.im 0
  · intro z
    change stripExtension T D (z + 1 - c) = stripExtension T D (z - c) + 1
    have he : z + 1 - c = z - c + 1 := by ring
    rw [he]
    exact extension_periodic T D hp (z - c)
  · intro z hz
    have hzi := (Complex.mem_reProdIm.mp hz).2
    have hs : z.im - c.im ∈ uIcc (0 : ℝ) (-c.im) := by
      rcases le_total c.im 0 with hi | hi
      · rw [uIcc_of_le hi] at hzi
        rw [uIcc_of_le (neg_nonneg.mpr hi)]
        constructor <;> linarith [hzi.1, hzi.2]
      · rw [uIcc_of_ge hi] at hzi
        rw [uIcc_of_ge (neg_nonpos.mpr hi)]
        constructor <;> linarith [hzi.1, hzi.2]
    have hsub : uIcc (0 : ℝ) (-c.im) ⊆ Ioo (-D) D :=
      ordConnected_Ioo.uIcc_subset (by constructor <;> linarith)
        (by
          change -D < -c.im ∧ -c.im < D
          exact abs_lt.mp (by simpa only [abs_neg] using hc))
    have hm : z - c ∈ symmetricStrip D := by
      change |(z - c).im| < D
      rw [Complex.sub_im]
      exact abs_lt.mpr (hsub hs)
    have hg : AnalyticAt ℂ (fun w : ℂ => w - c) z :=
      analyticAt_id.sub analyticAt_const
    exact ((extension_analytic T D ha (z - c) hm).comp_of_eq hg rfl).differentiableAt.differentiableWithinAt

theorem extension_continuous_real (T : ℂ → ℂ) (D : ℝ) (hD : 0 < D)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D)) :
    Continuous (fun x : ℝ => stripExtension T D (x : ℂ)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hx : (x : ℂ) ∈ symmetricStrip D := by
    simpa only [symmetricStrip, mem_ofPred_eq, Complex.ofReal_im, abs_zero] using hD
  exact (extension_analytic T D ha (x : ℂ) hx).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

/-- A complex shift changes the actual zero mode by the shift and every
nonzero mode by its exact exponential phase. -/
theorem coefficient_shift_on_strip (n : ℤ) (T : ℂ → ℂ) (D : ℝ) (δ : ℂ)
    (hD : 0 < D) (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z + 1) = T z + 1)
    (hδ : |δ.im| < D) :
    gateFourierCoefficient n 0 (fun w => T (w + δ)) =
      exp (Kneser.fourierFrequency n * δ) *
        (gateFourierCoefficient n 0 T + if n = 0 then δ else 0) := by
  have he : gateFourierCoefficient n 0 (fun w => T (w + δ)) =
      gateFourierCoefficient n 0 (centered (stripExtension T D) (-δ)) := by
    apply coefficient_eq_of_eq_on_real_gate
    intro x _
    have hx : (x : ℂ) + δ ∈ symmetricStrip D := by
      simpa only [symmetricStrip, mem_ofPred_eq, Complex.add_im,
        Complex.ofReal_im, zero_add] using hδ
    simp only [centered, sub_neg_eq_add, extension_eq T D _ hx]
  rw [he, ← centered_extension_height_eq_zero n T D (-δ) hD ha hp
    (by simpa only [Complex.neg_im, abs_neg] using hδ),
    coefficient_center_shift n (stripExtension T D) (-δ)
      (extension_periodic T D hp) (extension_continuous_real T D hD ha),
    coefficient_extension_eq n T D hD]
  by_cases hn : n = 0
  · simp [hn, Kneser.fourierFrequency]
  · simp [hn]

/-- The local map need only agree with the shifted global map on `[0,1]`.
No global periodicity or holomorphy of the local map is assumed. -/
theorem local_coefficient_shift_on_strip (n : ℤ) (Tlocal T : ℂ → ℂ)
    (D : ℝ) (δ : ℂ) (hD : 0 < D)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z + 1) = T z + 1)
    (hδ : |δ.im| < D)
    (he : ∀ x ∈ Icc (0 : ℝ) 1, Tlocal (x : ℂ) = T ((x : ℂ) + δ)) :
    gateFourierCoefficient n 0 Tlocal =
      exp (Kneser.fourierFrequency n * δ) *
        (gateFourierCoefficient n 0 T + if n = 0 then δ else 0) := by
  rw [coefficient_eq_of_eq_on_real_gate n Tlocal (fun w => T (w + δ)) he]
  exact coefficient_shift_on_strip n T D δ hD ha hp hδ

theorem local_zero_coefficient_shift (Tlocal T : ℂ → ℂ)
    (D : ℝ) (δ : ℂ) (hD : 0 < D)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z + 1) = T z + 1)
    (hδ : |δ.im| < D)
    (he : ∀ x ∈ Icc (0 : ℝ) 1, Tlocal (x : ℂ) = T ((x : ℂ) + δ)) :
    gateFourierCoefficient 0 0 Tlocal = gateFourierCoefficient 0 0 T + δ := by
  simpa only [Kneser.fourierFrequency, Int.cast_zero, mul_zero, zero_mul,
    exp_zero, one_mul, ↓reduceIte] using
    local_coefficient_shift_on_strip 0 Tlocal T D δ hD ha hp hδ he

theorem local_nonzero_coefficient_shift (n : ℤ) (hn : n ≠ 0)
    (Tlocal T : ℂ → ℂ) (D : ℝ) (δ : ℂ) (hD : 0 < D)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z + 1) = T z + 1)
    (hδ : |δ.im| < D)
    (he : ∀ x ∈ Icc (0 : ℝ) 1, Tlocal (x : ℂ) = T ((x : ℂ) + δ)) :
    gateFourierCoefficient n 0 Tlocal =
      exp (Kneser.fourierFrequency n * δ) * gateFourierCoefficient n 0 T := by
  simpa only [hn, ↓reduceIte, add_zero] using
    local_coefficient_shift_on_strip n Tlocal T D δ hD ha hp hδ he

/-- Exact gauge invariance for every nonzero integer mode, including modes
whose Fourier coefficient is zero. -/
theorem local_horn_gauge_invariant (n : ℤ) (hn : n ≠ 0)
    (Tlocal T : ℂ → ℂ) (D : ℝ) (δ : ℂ) (hD : 0 < D)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z + 1) = T z + 1)
    (hδ : |δ.im| < D)
    (he : ∀ x ∈ Icc (0 : ℝ) 1, Tlocal (x : ℂ) = T ((x : ℂ) + δ)) :
    gateFourierCoefficient n 0 Tlocal *
      exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0 Tlocal) =
    gateFourierCoefficient n 0 T *
      exp (-Kneser.fourierFrequency n * gateFourierCoefficient 0 0 T) := by
  rw [local_nonzero_coefficient_shift n hn Tlocal T D δ hD ha hp hδ he,
    local_zero_coefficient_shift Tlocal T D δ hD ha hp hδ he]
  have harg : -Kneser.fourierFrequency n * (gateFourierCoefficient 0 0 T + δ) =
      -Kneser.fourierFrequency n * gateFourierCoefficient 0 0 T -
        Kneser.fourierFrequency n * δ := by ring
  rw [harg, exp_sub]
  have hnz := exp_ne_zero (Kneser.fourierFrequency n * δ)
  field_simp

end Kneser.ActualFourierGaugeBridge
end
