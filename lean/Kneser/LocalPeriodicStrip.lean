import Kneser.GateFourierHeight
import Mathlib.Algebra.Order.Floor.Ring

/-!
An analytic periodic germ on the actual gate disc extends to a complete
horizontal strip. Integer-cell gluing is proved at the cell boundaries;
no global periodicity or strip analyticity is assumed.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.LocalPeriodicStrip

open Filter Set Metric Kneser.GateFourierDerivative
open scoped Topology Interval

def strip : Set ℂ := {z | |z.im| < 1}

def cell (z : ℂ) : ℤ := Int.floor z.re

def reduced (z : ℂ) : ℂ := z - (cell z : ℂ)

def periodize (f : ℂ → ℂ) (z : ℂ) : ℂ := f (reduced z)

def lift (T : ℂ → ℂ) (z : ℂ) : ℂ := T (reduced z) + (cell z : ℂ)

theorem strip_isOpen : IsOpen strip :=
  isOpen_lt (Complex.continuous_im.abs) continuous_const

theorem reduced_re (z : ℂ) : 0 ≤ (reduced z).re ∧ (reduced z).re < 1 := by
  have hlo := Int.floor_le z.re
  have hhi := Int.lt_floor_add_one z.re
  simp only [reduced, cell, Complex.sub_re, Complex.intCast_re]
  constructor <;> linarith

theorem reduced_im (z : ℂ) : (reduced z).im = z.im := by
  simp [reduced]

theorem reduced_mem_ball (z : ℂ) (hz : z ∈ strip) : reduced z ∈ ball (0 : ℂ) 2 := by
  obtain ⟨hlo, hhi⟩ := reduced_re z
  have hb := Complex.norm_le_abs_re_add_abs_im (reduced z)
  rw [abs_of_nonneg hlo, reduced_im] at hb
  change |z.im| < 1 at hz
  simp only [mem_ball, dist_zero_right]
  linarith

theorem cell_add_one (z : ℂ) : cell (z + 1) = cell z + 1 := by
  simp [cell]

theorem reduced_add_one (z : ℂ) : reduced (z + 1) = reduced z := by
  rw [reduced, cell_add_one, Int.cast_add, Int.cast_one]
  dsimp [reduced]
  ring

theorem periodize_periodic (f : ℂ → ℂ) (z : ℂ) : periodize f (z + 1) = periodize f z := by
  simp only [periodize, reduced_add_one]

theorem lift_translation (T : ℂ → ℂ) (z : ℂ) : lift T (z + 1) = lift T z + 1 := by
  simp only [lift, reduced_add_one, cell_add_one, Int.cast_add, Int.cast_one]
  ring

theorem periodize_germ (f : ℂ → ℂ)
    (hp : ∀ z ∈ ball (0 : ℂ) 2, f (z + 1) = f z)
    (w : ℂ) (hw : w ∈ strip) :
    periodize f =ᶠ[𝓝 w] (fun z => f (z - (cell w : ℂ))) := by
  let k : ℤ := cell w
  have hw2 : w - (k : ℂ) ∈ ball (0 : ℂ) 2 := reduced_mem_ball w hw
  have hc : ContinuousAt (fun z : ℂ => z - (k : ℂ)) w := continuousAt_id.sub continuousAt_const
  have hb : ∀ᶠ z in 𝓝 w, z - (k : ℂ) ∈ ball (0 : ℂ) 2 :=
    hc.eventually (isOpen_ball.mem_nhds hw2)
  have hre : (w - (k : ℂ)).re ∈ Ioo (-1 : ℝ) 2 := by
    obtain ⟨hlo, hhi⟩ := reduced_re w
    change 0 ≤ (w - (k : ℂ)).re at hlo
    change (w - (k : ℂ)).re < 1 at hhi
    constructor <;> linarith
  have hr : ∀ᶠ z in 𝓝 w, (z - (k : ℂ)).re ∈ Ioo (-1 : ℝ) 2 :=
    (Complex.continuous_re.continuousAt.comp hc).eventually (isOpen_Ioo.mem_nhds hre)
  filter_upwards [hb, hr, strip_isOpen.mem_nhds hw] with z hz2 hzre hzstrip
  have hlo : k - 1 ≤ cell z := by
    apply Int.le_floor.mpr
    have h := hzre.1
    simp only [Complex.sub_re, Complex.intCast_re] at h
    push_cast
    linarith
  have hhi : cell z < k + 2 := by
    apply Int.floor_lt.mpr
    have h := hzre.2
    simp only [Complex.sub_re, Complex.intCast_re] at h
    push_cast
    linarith
  have he : cell z = k - 1 ∨ cell z = k ∨ cell z = k + 1 := by omega
  obtain hminus | hzero | hplus := he
  · have heq : reduced z = (z - (k : ℂ)) + 1 := by
      simp only [reduced, hminus, Int.cast_sub, Int.cast_one]
      ring
    simpa only [periodize, heq] using hp _ hz2
  · simp only [periodize, reduced, hzero]
    rfl
  · have heq : z - (k : ℂ) = reduced z + 1 := by
      simp only [reduced, hplus, Int.cast_add, Int.cast_one]
      ring
    rw [heq]
    exact (hp _ (reduced_mem_ball z hzstrip)).symm

theorem periodize_analytic (f : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ f (ball (0 : ℂ) 4))
    (hp : ∀ z ∈ ball (0 : ℂ) 2, f (z + 1) = f z) :
    AnalyticOnNhd ℂ (periodize f) strip := by
  intro w hw
  have hg := periodize_germ f hp w hw
  have hred := ball_subset_ball (by norm_num : (2 : ℝ) ≤ 4) (reduced_mem_ball w hw)
  have hf := (ha _ hred).comp_of_eq (f := fun z : ℂ => z - (cell w : ℂ))
    (analyticAt_id.sub analyticAt_const) rfl
  exact hf.congr hg.symm

theorem lift_eq_periodize_displacement (T : ℂ → ℂ) (z : ℂ) :
    lift T z = z + periodize (fun w => T w - w) z := by
  dsimp [lift, periodize, reduced]
  ring

theorem lift_analytic (T : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ T (ball (0 : ℂ) 4))
    (hp : ∀ z ∈ ball (0 : ℂ) 2, T (z + 1) = T z + 1) :
    AnalyticOnNhd ℂ (lift T) strip := by
  have hperiod : ∀ z ∈ ball (0 : ℂ) 2, (T (z + 1) - (z + 1)) = T z - z := by
    intro z hz
    rw [hp z hz]
    ring
  have hh := periodize_analytic (fun z => T z - z) (fun z hz => (ha z hz).sub analyticAt_id) hperiod
  intro z hz
  have he : lift T = (fun w => w + periodize (fun v => T v - v) w) :=
    funext (lift_eq_periodize_displacement T)
  rw [he]
  exact analyticAt_id.add (hh z hz)

theorem reduced_real_of_unit_interval (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    reduced (x : ℂ) = x := by
  have hc : cell (x : ℂ) = 0 := by
    apply Int.floor_eq_zero_iff.mpr
    exact ⟨hx.1.le, hx.2⟩
  simp [reduced, hc]

theorem gateFourier_zero_lift_eq (n : ℤ) (T : ℂ → ℂ) :
    gateFourierCoefficient n 0 (lift T) = gateFourierCoefficient n 0 T := by
  unfold gateFourierCoefficient
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  have hc : cell (x : ℂ) = 0 := Int.floor_eq_zero_iff.mpr ⟨hx'.1.le, hx'.2⟩
  simp only [gatePoint, Complex.ofReal_zero, mul_zero, add_zero, lift,
    reduced_real_of_unit_interval x hx', hc, Int.cast_zero, add_zero]

theorem gateCorrection_zero_periodize_eq (n : ℤ) (D : ℂ → ℂ) :
    gateCorrectionCoefficient n 0 (periodize D) = gateCorrectionCoefficient n 0 D := by
  unfold gateCorrectionCoefficient
  apply intervalIntegral.integral_congr_uIoo
  intro x hx
  have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa only [uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
  simp only [gatePoint, Complex.ofReal_zero, mul_zero, add_zero, periodize,
    reduced_real_of_unit_interval x hx']

theorem lift_remainder (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (s : ℝ) (z : ℂ) :
    lift (T s) z - lift (T 0) z - (s : ℂ) * periodize D z =
      T s (reduced z) - T 0 (reduced z) - (s : ℂ) * D (reduced z) := by
  dsimp [lift, periodize]
  ring

theorem gateFourier_height_eq_zero (n : ℤ) (T : ℂ → ℂ)
    (ha : AnalyticOnNhd ℂ T (ball (0 : ℂ) 4))
    (hp : ∀ z ∈ ball (0 : ℂ) 2, T (z + 1) = T z + 1)
    (Y : ℝ) (hY : |Y| < 1) :
    gateFourierCoefficient n Y (lift T) = gateFourierCoefficient n 0 T := by
  rw [← gateFourier_zero_lift_eq n T]
  apply Kneser.GateFourierHeight.gateFourier_height_independent n (lift T) Y 0
    (lift_translation T)
  intro z hz
  have hy : z.im ∈ uIcc Y 0 := (Complex.mem_reProdIm.mp hz).2
  have hs : z ∈ strip := by
    change |z.im| < 1
    have hi : uIcc Y 0 ⊆ Ioo (-1 : ℝ) 1 := by
      exact ordConnected_Ioo.uIcc_subset (abs_lt.mp hY) (by constructor <;> norm_num)
    exact abs_lt.mpr (hi hy)
  exact ((lift_analytic T ha hp) z hs).differentiableAt.differentiableWithinAt

end Kneser.LocalPeriodicStrip
end
