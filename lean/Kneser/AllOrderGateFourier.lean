import Kneser.AllOrderCompactGate
import Kneser.DiscGateFourier

/-! Every finite integer expansion is extracted by the genuine Fourier
interval integral. The zeroth coefficient includes subtraction of the
identity; every higher coefficient is the integral of the actual spatial
Taylor coefficient. Integrability is derived from spatial holomorphy. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderGateFourier

open Filter Set Metric MeasureTheory
open scoped Topology BigOperators
open Kneser.FiniteExpansionHolomorphy Kneser.AllOrderCompactGate
open Kneser.GateFourierDerivative Kneser.DiscGateFourier

def scalarPolynomial (c : ℕ → ℂ) (m : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), s ^ j * c j

def ScalarExpansion (f : ℝ → ℂ) (c : ℕ → ℂ) (m : ℕ) : Prop :=
  c 0 = f 0 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
    ‖f s - scalarPolynomial c m (s : ℂ)‖ ≤ C * s ^ (m + 1)

def displacementCoefficient (b : ℕ → ℂ → ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  b j z - if j = 0 then z else 0

def fourierCoefficient (n : ℤ) (b : ℕ → ℂ → ℂ) (j : ℕ) : ℂ :=
  gateCorrectionCoefficient n 0 (displacementCoefficient b j)

theorem displacementCoefficient_zero (b : ℕ → ℂ → ℂ) :
    displacementCoefficient b 0 = fun z => b 0 z - z := by
  funext z
  simp [displacementCoefficient]

theorem displacementCoefficient_succ (b : ℕ → ℂ → ℂ) (j : ℕ) :
    displacementCoefficient b (j + 1) = b (j + 1) := by
  funext z
  simp [displacementCoefficient]

theorem fourierCoefficient_zero (n : ℤ) (b : ℕ → ℂ → ℂ) :
    fourierCoefficient n b 0 = gateFourierCoefficient n 0 (b 0) := by
  rw [fourierCoefficient, displacementCoefficient_zero]
  rfl

theorem fourierCoefficient_succ (n : ℤ) (b : ℕ → ℂ → ℂ) (j : ℕ) :
    fourierCoefficient n b (j + 1) = gateCorrectionCoefficient n 0 (b (j + 1)) := by
  rw [fourierCoefficient, displacementCoefficient_succ]

theorem polynomial_displacement (b : ℕ → ℂ → ℂ) (m : ℕ) (s z : ℂ) :
    complexPolynomial (displacementCoefficient b) m s z = complexPolynomial b m s z - z := by
  simp [complexPolynomial, displacementCoefficient, mul_sub, Finset.sum_sub_distrib]

theorem polynomial_integral (n : ℤ) (b : ℕ → ℂ → ℂ) (m : ℕ) (s : ℂ)
    (hb : ∀ j ≤ m, AnalyticOnNhd ℂ (b j) (ball (0 : ℂ) 4)) :
    gateCorrectionCoefficient n 0 (complexPolynomial (displacementCoefficient b) m s) =
      scalarPolynomial (fourierCoefficient n b) m s := by
  have hi (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      IntervalIntegrable (fun x => displacementCoefficient b j (gatePoint 0 x) * gateWeight n 0 x)
        volume 0 1 := by
    apply intervalIntegrable_of_disc_analytic
    intro z hz
    unfold displacementCoefficient
    split_ifs <;> exact (hb j (by simpa using Finset.mem_range.mp hj) z hz).sub
      (by first | exact analyticAt_id | exact analyticAt_const)
  unfold gateCorrectionCoefficient complexPolynomial scalarPolynomial fourierCoefficient
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    simp_rw [mul_assoc]
    exact intervalIntegral.integral_const_mul _ _
  · intro j hj
    simpa only [mul_assoc] using (hi j hj).const_mul (s ^ j)

theorem gateFourier_scalarExpansion (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ)
    (hpacket : FinitePacket T b m (ball (0 : ℂ) 4))
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) (ball (0 : ℂ) 4)) :
    ∀ n : ℤ, ScalarExpansion (fun s => gateFourierCoefficient n 0 (T s))
      (fourierCoefficient n b) m := by
  let K : Set ℂ := gatePoint 0 '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image (by
    change Continuous (fun x : ℝ => (x : ℂ) + Complex.I * (0 : ℂ))
    simpa using Complex.continuous_ofReal)
  have hKU : K ⊆ ball (0 : ℂ) 4 := by
    rintro z ⟨x, hx, rfl⟩
    exact real_gate_mem_disc x hx
  obtain ⟨C, hC, hExpansion⟩ := hpacket.2.2 K hK hKU
  intro n
  refine ⟨?_, C, hC, ?_⟩
  · rw [fourierCoefficient_zero]
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
    dsimp only
    rw [hpacket.2.1 _ (real_gate_mem_disc x hx')]
  · filter_upwards [hT, hExpansion] with s hs hse
    have hiT := intervalIntegrable_of_disc_analytic n (fun z => T s z - z)
      (fun z hz => (hs z hz).sub analyticAt_id)
    have hip := intervalIntegrable_of_disc_analytic n
      (complexPolynomial (displacementCoefficient b) m (s : ℂ)) (by
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
    rw [← polynomial_integral n b m (s : ℂ) hpacket.1]
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

end Kneser.AllOrderGateFourier

end
