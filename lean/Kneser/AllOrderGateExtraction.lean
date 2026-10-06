import Kneser.AllOrderHornExpansion

/-! Fourier and horn extraction need only a neighborhood of the true
integration segment. This version accepts any source domain containing
that segment, including the actual centered image disc of radius three. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderGateExtraction

open Filter Set Metric MeasureTheory
open scoped Topology BigOperators
open Kneser.AllOrderGateFourier Kneser.AllOrderHornExpansion Kneser.AllOrderCompactGate
open Kneser.FiniteExpansionHolomorphy Kneser.GateFourierDerivative

theorem intervalIntegrable_of_gate_analytic (n : ℤ) (f : ℂ → ℂ) (U : Set ℂ)
    (hGate : ∀ x ∈ Icc (0 : ℝ) 1, gatePoint 0 x ∈ U)
    (ha : AnalyticOnNhd ℂ f U) :
    IntervalIntegrable (fun x => f (gatePoint 0 x) * gateWeight n 0 x) volume 0 1 := by
  have hf : ContinuousOn (fun x : ℝ => f (gatePoint 0 x)) (Icc (0 : ℝ) 1) := by
    intro x hx
    have hg : ContinuousAt (fun y : ℝ => gatePoint 0 y) x := by
      simpa only [gatePoint, Complex.ofReal_zero, mul_zero, add_zero] using
        Complex.continuous_ofReal.continuousAt
    exact ((ha _ (hGate x hx)).continuousAt.comp hg).continuousWithinAt
  have hw : Continuous (fun x : ℝ => gateWeight n 0 x) := by
    simpa only [gateWeight, gatePoint, Complex.ofReal_zero, mul_zero, add_zero,
      Pi.mul_apply] using (continuous_const.mul Complex.continuous_ofReal).cexp
  exact (hf.mul hw.continuousOn).intervalIntegrable_of_Icc (by norm_num)

theorem polynomial_integral_of_gate (n : ℤ) (b : ℕ → ℂ → ℂ) (m : ℕ) (s : ℂ) (U : Set ℂ)
    (hGate : ∀ x ∈ Icc (0 : ℝ) 1, gatePoint 0 x ∈ U)
    (hb : ∀ j ≤ m, AnalyticOnNhd ℂ (b j) U) :
    gateCorrectionCoefficient n 0 (complexPolynomial (displacementCoefficient b) m s) =
      scalarPolynomial (fourierCoefficient n b) m s := by
  have hi (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      IntervalIntegrable (fun x => displacementCoefficient b j (gatePoint 0 x) * gateWeight n 0 x)
        volume 0 1 := by
    apply intervalIntegrable_of_gate_analytic n _ U hGate
    intro z hz
    unfold displacementCoefficient
    split_ifs <;> exact (hb j (by simpa using Finset.mem_range.mp hj) z hz).sub
      (by first | exact analyticAt_id | exact analyticAt_const)
  unfold gateCorrectionCoefficient complexPolynomial scalarPolynomial fourierCoefficient
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    simp_rw [mul_assoc]
    exact intervalIntegral.integral_const_mul _ _
  · intro j hj
    simpa only [mul_assoc] using (hi j hj).const_mul (s ^ j)

theorem gateFourier_scalarExpansion_of_set (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ)
    (U : Set ℂ) (hGate : ∀ x ∈ Icc (0 : ℝ) 1, gatePoint 0 x ∈ U)
    (hpacket : FinitePacket T b m U)
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) U) :
    ∀ n : ℤ, ScalarExpansion (fun s => gateFourierCoefficient n 0 (T s))
      (fourierCoefficient n b) m := by
  let K : Set ℂ := gatePoint 0 '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by
    change Continuous (fun x : ℝ => (x : ℂ) + Complex.I * (0 : ℂ))
    simpa using Complex.continuous_ofReal)
  have hKU : K ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact hGate x hx
  obtain ⟨C, hC, hExpansion⟩ := hpacket.2.2 K hK hKU
  intro n
  refine ⟨?_, C, hC, ?_⟩
  · rw [fourierCoefficient_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    dsimp only
    rw [hpacket.2.1 _ (hGate x hx')]
  · filter_upwards [hT, hExpansion] with s hs hse
    have hiT := intervalIntegrable_of_gate_analytic n (fun z => T s z - z) U hGate
      (fun z hz => (hs z hz).sub analyticAt_id)
    have hip := intervalIntegrable_of_gate_analytic n
      (complexPolynomial (displacementCoefficient b) m (s : ℂ)) U hGate (by
        intro z hz
        have ha : AnalyticAt ℂ (fun z => complexPolynomial b m (s : ℂ) z) z := by
          have he : (fun z => complexPolynomial b m (s : ℂ) z) =
              ∑ j ∈ Finset.range (m + 1), (fun z => (s : ℂ) ^ j * b j z) := by
            funext z
            simp [complexPolynomial, Finset.sum_apply]
          rw [he]
          apply Finset.analyticAt_sum
          intro j hj
          exact analyticAt_const.mul (hpacket.1 j (by simpa using Finset.mem_range.mp hj) z hz)
        have he : complexPolynomial (displacementCoefficient b) m (s : ℂ) =
            fun z => complexPolynomial b m (s : ℂ) z - z := by
          funext z
          exact polynomial_displacement b m (s : ℂ) z
        rw [he]
        exact ha.sub analyticAt_id)
    rw [← polynomial_integral_of_gate n b m (s : ℂ) U hGate hpacket.1]
    unfold gateFourierCoefficient gateCorrectionCoefficient
    rw [← intervalIntegral.integral_sub hiT hip]
    have heq (x : ℝ) :
        (T s (gatePoint 0 x) - gatePoint 0 x) * gateWeight n 0 x -
          complexPolynomial (displacementCoefficient b) m (s : ℂ) (gatePoint 0 x) * gateWeight n 0 x =
        (T s (gatePoint 0 x) - complexPolynomial b m (s : ℂ) (gatePoint 0 x)) * gateWeight n 0 x := by
      rw [polynomial_displacement]
      ring
    simp_rw [heq]
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := C * s ^ (m + 1))
      (f := fun x => (T s (gatePoint 0 x) - complexPolynomial b m (s : ℂ) (gatePoint 0 x)) *
        gateWeight n 0 x) (by
          intro x hx
          have hx' : x ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self
            (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)
          rw [norm_mul, norm_gateWeight]
          simp only [mul_zero, Real.exp_zero, mul_one]
          exact hse _ ⟨x, hx', rfl⟩)
    simpa using hh

theorem gate_horn_all_orders_of_set (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ)
    (U : Set ℂ) (hGate : ∀ x ∈ Icc (0 : ℝ) 1, gatePoint 0 x ∈ U)
    (hpacket : FinitePacket T b m U)
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) U) :
    ∀ n : ℤ,
      ScalarExpansion (Kneser.realHornCoefficient n
        (fun s => gateFourierCoefficient n 0 (T s))
        (fun s => gateFourierCoefficient 0 0 (T s)))
        (Kneser.CauchyHigherTaylor.coefficient
          (hornReference n (fourierCoefficient n b) (fourierCoefficient 0 b) m)) m ∧
      (gateFourierCoefficient n 0 (T 0) ≠ 0 →
        ScalarExpansion (fun s => Complex.log (Kneser.realNormalizedHornCoefficient n
          (fun t => gateFourierCoefficient n 0 (T t))
          (fun t => gateFourierCoefficient 0 0 (T t)) s))
          (Kneser.CauchyHigherTaylor.coefficient
            (logReference n (fourierCoefficient n b) (fourierCoefficient 0 b) m)) m ∧
        (∀ᶠ s : ℝ in 𝓝[>] 0, Kneser.realNormalizedHornCoefficient n
          (fun t => gateFourierCoefficient n 0 (T t))
          (fun t => gateFourierCoefficient 0 0 (T t)) s ∈ Complex.slitPlane) ∧
        Kneser.CauchyHigherTaylor.coefficient
          (logReference n (fourierCoefficient n b) (fourierCoefficient 0 b) m) 0 = 0) := by
  have hf := gateFourier_scalarExpansion_of_set T b m U hGate hpacket hT
  intro n
  exact ⟨raw_horn_scalarExpansion n _ _ _ _ m (hf n) (hf 0),
    fun hB => log_horn_scalarExpansion n _ _ _ _ m (hf n) (hf 0) hB⟩

theorem real_gate_mem_ball_three (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    gatePoint 0 x ∈ ball (0 : ℂ) 3 := by
  simp only [gatePoint, Complex.ofReal_zero, mul_zero, add_zero, mem_ball,
    dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
  linarith [hx.2]

end Kneser.AllOrderGateExtraction

end
