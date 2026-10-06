import Kneser.HigherPreparedModelTime
import Kneser.ReflectedPreparedModel

/-! The actual reflected logarithmic model and finite correction at every
preparation degree.  Reflection is algebraic, and the inverse one-step
identity follows from the genuine exponential inverse and logarithm branch
conditions. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Kneser.ReflectedHigherModelTime

open Kneser.ExponentialPreparedHigher Kneser.HigherPreparedModelTime
open Kneser.ExponentialModelTime Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.PreparedTwoRootDivision
open Kneser.ExponentialPreparedQuadratic
open Kneser.ExponentialUnfolding Kneser.RepellingExponentialOrbit
open Kneser.AnalyticEvenDescent Kneser.ReflectedPreparedModel
open Kneser.ParabolicFatouCoordinate (log_mul_of_re_pos)
open Filter Set Metric
open scoped Topology BigOperators

def reflectedCorrection (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ) :
    Fin (2 * n) → ℂ → ℂ := fun i s => (-1 : ℂ) ^ i.val * e i s

theorem reflectedCorrection_analytic (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (he : ∀ i, AnalyticAt ℂ (e i) 0) :
    ∀ i, AnalyticAt ℂ (reflectedCorrection n e i) 0 :=
  fun i => analyticAt_const.mul (he i)

theorem correction_reflected (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ) (s v : ℂ) :
    correction n (reflectedCorrection n e) s v = -correction n e s (-v) := by
  unfold correction reflectedCorrection
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [neg_pow, pow_succ]
  ring

def modelTime (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (s v : ℂ) : ℂ :=
  HigherPreparedModelTime.modelTime (-U) (-H) n (reflectedCorrection n e) s v

theorem analyticAt_parameter {U H : ℂ → ℂ} (n : ℕ)
    (e : Fin (2 * n) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0) (v : ℂ) (hv : v.re < 0) :
    AnalyticAt ℂ (fun s => modelTime U H n e s v) 0 := by
  have hs := HigherPreparedModelTime.analyticAt_splitModelTime n (reflectedCorrection n e)
    hU.neg (by simpa using hU0) hH.neg (by simpa using hHne)
    (reflectedCorrection_analytic n e he) v hv
  have hc : AnalyticAt ℂ (fun x => HigherPreparedModelTime.splitModelTime
      (-U) (-H) n (reflectedCorrection n e) (x, v)) 0 :=
    hs.comp_of_eq (analyticAt_id.prod analyticAt_const) (by simp)
  have hd := analyticAt_even_sqrt
    (fun x => HigherPreparedModelTime.splitModelTime_even (-U) (-H) n
      (reflectedCorrection n e) x v) hc
  simpa only [HigherPreparedModelTime.splitModelTime_sqrt, modelTime] using hd

theorem exists_compact_disc_bounds {U H : ℂ → ℂ} (n : ℕ)
    (e : Fin (2 * n) → ℂ → ℂ)
    (hU : AnalyticAt ℂ U 0) (hU0 : U 0 = 0)
    (hH : AnalyticAt ℂ H 0) (hHne : H 0 ≠ 0)
    (he : ∀ i, AnalyticAt ℂ (e i) 0)
    (S : Set ℂ) (hS : IsCompact S) (hneg : ∀ v ∈ S, v.re < 0) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ v ∈ S,
      DiffContOnCl ℂ (fun s => modelTime U H n e s v) (ball 0 r) ∧
      (∀ s ∈ closedBall (0 : ℂ) r, ‖modelTime U H n e s v‖ ≤ M) := by
  exact HigherPreparedModelTime.exists_compact_modelTime_disc_bounds n
    (reflectedCorrection n e) hU.neg (by simpa using hU0) hH.neg
    (by simpa using hHne) (reflectedCorrection_analytic n e he) S hS hneg

theorem residue_pair (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x v : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0) :
    modelTime U H n e (x ^ 2) v =
      -Complex.log (-U x - v) / Complex.log (rootMultiplier U x) -
      Complex.log (-U (-x) - v) / Complex.log (rootMultiplier U (-x)) -
      correction n e (x ^ 2) (-v) := by
  have hraw := reflected_preparedModelTime_residue_pair U H
    (fun _ => 0) (fun _ => 0) hH x v hx hHx hHnx
  simp only [preparedModelTime, polynomialCorrection,
    Pi.neg_apply, neg_zero, zero_mul, zero_add, add_zero, sub_zero] at hraw
  dsimp [modelTime, HigherPreparedModelTime.modelTime]
  rw [hraw, correction_reflected]
  ring

theorem one_step (U H : ℂ → ℂ) (n : ℕ) (e : Fin (2 * n) → ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x v F : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0)
    (hs : x ^ 2 ≠ 1) (hv : ‖v‖ < 1)
    (hf : unfolding (x ^ 2) (-reflectedInverse (x ^ 2) v) + reflectedInverse (x ^ 2) v =
      rootProduct U x (-reflectedInverse (x ^ 2) v) *
        symmetricCofactor U x (-reflectedInverse (x ^ 2) v))
    (hF : F =
      Complex.log (1 + (-reflectedInverse (x ^ 2) v - U (-x)) *
        symmetricCofactor U x (-reflectedInverse (x ^ 2) v)) /
        Complex.log (rootMultiplier U x) +
      Complex.log (1 + (-reflectedInverse (x ^ 2) v - U x) *
        symmetricCofactor U x (-reflectedInverse (x ^ 2) v)) /
        Complex.log (rootMultiplier U (-x)) - 1)
    (ha : 0 < (-U x - reflectedInverse (x ^ 2) v).re)
    (hb : 0 < (-U (-x) - reflectedInverse (x ^ 2) v).re)
    (hra : 0 < (1 + (-reflectedInverse (x ^ 2) v - U (-x)) *
      symmetricCofactor U x (-reflectedInverse (x ^ 2) v)).re)
    (hrb : 0 < (1 + (-reflectedInverse (x ^ 2) v - U x) *
      symmetricCofactor U x (-reflectedInverse (x ^ 2) v)).re) :
    modelTime U H n e (x ^ 2) (reflectedInverse (x ^ 2) v) -
      modelTime U H n e (x ^ 2) v - 1 =
      F + correction n e (x ^ 2) (-v) -
        correction n e (x ^ 2) (-reflectedInverse (x ^ 2) v) := by
  have hlog := reflected_preparedModelTime_one_step U H (fun _ => 0) (fun _ => 0)
    hH x v F hx hHx hHnx hs hv hf hF ha hb hra hrb
  simp only [preparedModelTime, polynomialCorrection,
    Pi.neg_apply, neg_zero, zero_mul, zero_add, add_zero, sub_zero] at hlog
  dsimp [modelTime, HigherPreparedModelTime.modelTime]
  rw [correction_reflected, correction_reflected]
  linear_combination hlog

end Kneser.ReflectedHigherModelTime

end
