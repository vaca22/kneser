import Kneser.WeightedFourierExponential
import Mathlib.Topology.MetricSpace.Contracting

/-!
The W2 negative-mode equation is solved in the actual weighted Wiener
space.  The inputs below are quantitative Fourier decay budgets; neither
a solution of the sewing equation nor its coefficient comparison is an input.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

def valueBudget (H ρ : ℝ) (t : ℤ → ℂ) (m : ℤ) : ℝ :=
  ‖t m‖ * weight H m * Real.exp (‖Kneser.fourierFrequency m‖ * ρ)

def derivativeBudget (H ρ : ℝ) (t : ℤ → ℂ) (m : ℤ) : ℝ :=
  valueBudget H ρ t m * ‖Kneser.fourierFrequency m‖

def compositionTerm (H : ℝ) (hH : 0 ≤ H) (t : ℤ → ℂ) (Q : Space) (m : ℤ) : Space :=
  t m • shift H hH m (exponential H hH (Kneser.fourierFrequency m • Q))

def composition (H : ℝ) (hH : 0 ≤ H) (t : ℤ → ℂ) (Q : Space) : Space :=
  ∑' m : ℤ, compositionTerm H hH t Q m

theorem norm_compositionTerm_le (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (Q : Space) (hQ : ‖Q‖ ≤ ρ) (m : ℤ) :
    ‖compositionTerm H hH t Q m‖ ≤ valueBudget H ρ t m := by
  rw [compositionTerm, norm_smul]
  calc
    _ ≤ ‖t m‖ * (weight H m * Real.exp ‖Kneser.fourierFrequency m • Q‖) :=
      mul_le_mul_of_nonneg_left
        ((norm_shift_le H hH m _).trans
          (mul_le_mul_of_nonneg_left (norm_exponential_le H hH _) (weight_pos H m).le))
        (norm_nonneg _)
    _ ≤ valueBudget H ρ t m := by
      rw [norm_smul, valueBudget, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hQ (norm_nonneg _)))
          (weight_pos H m).le) (norm_nonneg _)

theorem summable_composition (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) :
    Summable (compositionTerm H hH t Q) :=
  Summable.of_norm_bounded hv (norm_compositionTerm_le H hH ρ t Q hQ)

theorem norm_composition_le (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) :
    ‖composition H hH t Q‖ ≤ ∑' m : ℤ, valueBudget H ρ t m := by
  have hs := hv.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_compositionTerm_le H hH ρ t Q hQ)
  exact (norm_tsum_le_tsum_norm hs).trans
    (hs.tsum_le_tsum (norm_compositionTerm_le H hH ρ t Q hQ) hv)

theorem norm_compositionTerm_sub_le (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℤ → ℂ) (Q R : Space) (hQ : ‖Q‖ ≤ ρ) (hR : ‖R‖ ≤ ρ) (m : ℤ) :
    ‖compositionTerm H hH t Q m - compositionTerm H hH t R m‖ ≤
      derivativeBudget H ρ t m * ‖Q - R‖ := by
  have he : shift H hH m (exponential H hH (Kneser.fourierFrequency m • Q)) -
      shift H hH m (exponential H hH (Kneser.fourierFrequency m • R)) =
      shift H hH m (exponential H hH (Kneser.fourierFrequency m • Q) -
        exponential H hH (Kneser.fourierFrequency m • R)) :=
    ((shiftCLM H hH m).map_sub _ _).symm
  rw [compositionTerm, compositionTerm, ← smul_sub, norm_smul, he]
  have hex := norm_exponential_sub_le H hH
    (Kneser.fourierFrequency m • Q) (Kneser.fourierFrequency m • R)
    (‖Kneser.fourierFrequency m‖ * ρ) (mul_nonneg (norm_nonneg _) hρ)
    (by rw [norm_smul]; exact mul_le_mul_of_nonneg_left hQ (norm_nonneg _))
    (by rw [norm_smul]; exact mul_le_mul_of_nonneg_left hR (norm_nonneg _))
  calc
    _ ≤ ‖t m‖ * (weight H m *
        (‖Kneser.fourierFrequency m • Q - Kneser.fourierFrequency m • R‖ *
          Real.exp (‖Kneser.fourierFrequency m‖ * ρ))) :=
      mul_le_mul_of_nonneg_left
        ((norm_shift_le H hH m _).trans (mul_le_mul_of_nonneg_left hex (weight_pos H m).le))
        (norm_nonneg _)
    _ = derivativeBudget H ρ t m * ‖Q - R‖ := by
      rw [← smul_sub, norm_smul, derivativeBudget, valueBudget]
      ring

theorem norm_composition_sub_le (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (hd : Summable (derivativeBudget H ρ t))
    (Q R : Space) (hQ : ‖Q‖ ≤ ρ) (hR : ‖R‖ ≤ ρ) :
    ‖composition H hH t Q - composition H hH t R‖ ≤
      (∑' m : ℤ, derivativeBudget H ρ t m) * ‖Q - R‖ := by
  have hbound := norm_compositionTerm_sub_le H hH ρ hρ t Q R hQ hR
  have hs := (hd.mul_right ‖Q - R‖).of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  rw [composition, composition,
    ← (summable_composition H hH ρ t hv Q hQ).tsum_sub
      (summable_composition H hH ρ t hv R hR)]
  exact (norm_tsum_le_tsum_norm hs).trans
    ((hs.tsum_le_tsum hbound (hd.mul_right _)).trans_eq (tsum_mul_right))

def sewingOperator (H : ℝ) (hH : 0 ≤ H) (t : ℤ → ℂ) (Q : Space) : Space :=
  -negativeProjection (composition H hH t Q)

/-- A Fourier decay certificate is sufficient to construct the negative
correction.  The contraction inequality is verified from the exponential
series, and the conclusion includes the exact coefficient-space equation. -/
theorem exists_sewing (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (hd : Summable (derivativeBudget H ρ t))
    (hvsum : (∑' m : ℤ, valueBudget H ρ t m) ≤ ρ)
    (hdsum : (∑' m : ℤ, derivativeBudget H ρ t m) ≤ (1 / 2 : ℝ)) :
    ∃ Q P : Space, Q ∈ Negative ∧ ‖Q‖ ≤ ρ ∧
      (∀ n : ℤ, n < 0 → P n = 0) ∧ ‖P‖ ≤ ρ ∧
      Q = -negativeProjection (composition H hH t Q) ∧
      P = positiveProjection (composition H hH t Q) ∧
      Q + composition H hH t Q = P := by
  let f := sewingOperator H hH t
  have hm : MapsTo f (negativeBall ρ) (negativeBall ρ) := by
    intro Q hQ
    refine ⟨?_, ?_⟩
    · intro n hn
      simp only [f, sewingOperator, lp.coeFn_neg, Pi.neg_apply]
      rw [(negativeProjection_mem _) n hn, neg_zero]
    · rw [mem_closedBall, dist_zero_right]
      change ‖-negativeProjection (composition H hH t Q)‖ ≤ ρ
      rw [norm_neg]
      exact (norm_negativeProjection_le _).trans
        ((norm_composition_le H hH ρ t hv Q (by simpa using hQ.2)).trans hvsum)
  have hc : ContractingWith (1 / 2 : NNReal) (hm.restrict f _ _) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro Q R
    change dist (f Q.val) (f R.val) ≤ _ * dist Q.val R.val
    rw [dist_eq_norm, dist_eq_norm]
    change ‖-negativeProjection (composition H hH t Q.val) -
      -negativeProjection (composition H hH t R.val)‖ ≤ _
    have he : -negativeProjection (composition H hH t Q.val) -
        -negativeProjection (composition H hH t R.val) =
        -(negativeProjection (composition H hH t Q.val) -
          negativeProjection (composition H hH t R.val)) := by abel
    rw [he, norm_neg, ← negativeProjection.map_sub]
    have hQ : ‖Q.val‖ ≤ ρ := by simpa using Q.property.2
    have hR : ‖R.val‖ ≤ ρ := by simpa using R.property.2
    exact (norm_negativeProjection_le _).trans
      ((norm_composition_sub_le H hH ρ hρ t hv hd Q.val R.val hQ hR).trans
        (by exact_mod_cast mul_le_mul_of_nonneg_right hdsum (norm_nonneg _)))
  obtain ⟨Q, hQ, hfixed, _, _⟩ := ContractingWith.exists_fixedPoint'
    (isComplete_negativeBall ρ) hm hc (zero_mem_negativeBall ρ hρ) (edist_ne_top 0 (f 0))
  let P := positiveProjection (composition H hH t Q)
  have hnorm : ‖Q‖ ≤ ρ := by simpa using hQ.2
  refine ⟨Q, P, hQ.1, hnorm, ?_, ?_, hfixed.symm, rfl, ?_⟩
  · intro n hn
    simp [P, not_le.mpr hn]
  · exact (norm_positiveProjection_le _).trans
      ((norm_composition_le H hH ρ t hv Q hnorm).trans hvsum)
  · change Q + composition H hH t Q = positiveProjection _
    calc
      _ = -negativeProjection (composition H hH t Q) + composition H hH t Q :=
        congrArg (fun a => a + composition H hH t Q) hfixed.symm
      _ = -negativeProjection (composition H hH t Q) +
          (negativeProjection (composition H hH t Q) +
            positiveProjection (composition H hH t Q)) :=
        congrArg (fun a => -negativeProjection (composition H hH t Q) + a)
          (projection_split (composition H hH t Q)).symm
      _ = _ := by abel

def periodicFunction (t : ℤ → ℂ) (z : ℂ) : ℂ := ∑' m : ℤ, t m * mode m z

theorem evaluate_composition (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (Q : Space) (hQ : ‖Q‖ ≤ ρ) (z : ℂ) (hz : |z.im| ≤ H) :
    evaluate H (composition H hH t Q) z = periodicFunction t (z + evaluate H Q z) := by
  change evaluateCLM H z hz (∑' m : ℤ, compositionTerm H hH t Q m) = _
  rw [(evaluateCLM H z hz).map_tsum (summable_composition H hH ρ t hv Q hQ)]
  simp only [compositionTerm, map_smul, evaluateCLM_apply, evaluate_shift,
    evaluate_exponential H hH _ z hz, smul_eq_mul]
  have he (m : ℤ) : evaluate H (Kneser.fourierFrequency m • Q) z =
      Kneser.fourierFrequency m * evaluate H Q z := by
    change evaluateCLM H z hz (Kneser.fourierFrequency m • Q) = _
    rw [map_smul, evaluateCLM_apply, smul_eq_mul]
  simp only [he, periodicFunction]
  apply tsum_congr
  intro m
  simp only [periodicFunction, mode, mul_add, Complex.exp_add]

/-- The Banach solution gives the nonlinear W2 sewing identity as an
identity of actual evaluated Fourier series on the common closed strip. -/
theorem exists_nonlinear_sewing (H : ℝ) (hH : 0 ≤ H) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (t : ℤ → ℂ) (hv : Summable (valueBudget H ρ t))
    (hd : Summable (derivativeBudget H ρ t))
    (hvsum : (∑' m : ℤ, valueBudget H ρ t m) ≤ ρ)
    (hdsum : (∑' m : ℤ, derivativeBudget H ρ t m) ≤ (1 / 2 : ℝ)) :
    ∃ Q P : Space, Q ∈ Negative ∧ ‖Q‖ ≤ ρ ∧
      (∀ n : ℤ, n < 0 → P n = 0) ∧ ‖P‖ ≤ ρ ∧
      P = positiveProjection (composition H hH t Q) ∧
      Q = -negativeProjection (composition H hH t Q) ∧
      (∀ z : ℂ, |z.im| ≤ H → ∀ t₀ : ℂ,
        (z + evaluate H Q z) + t₀ + periodicFunction t (z + evaluate H Q z) =
          z + t₀ + evaluate H P z) := by
  obtain ⟨Q, P, hneg, hQ, hpos, hP, hfixed, hproj, heq⟩ :=
    exists_sewing H hH ρ hρ t hv hd hvsum hdsum
  refine ⟨Q, P, hneg, hQ, hpos, hP, hproj, hfixed, ?_⟩
  intro z hz t₀
  have he := congrArg (evaluateCLM H z hz) heq
  simp only [map_add, evaluateCLM_apply, evaluate_composition H hH ρ t hv Q hQ z hz] at he
  calc
    _ = z + t₀ + (evaluate H Q z + periodicFunction t (z + evaluate H Q z)) := by ring
    _ = _ := by rw [he]

end Kneser.FourierSewing

end
