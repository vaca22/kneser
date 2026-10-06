import Kneser.AllOrderScalarAnalytic

/-! The all-orders gauge invariant horn coefficient and its normalized
principal logarithm. Genuine one-sided Fourier coefficients are compared
with finite analytic polynomials. The principal logarithm's common local
branch is proved from convergence to one and requires only the selected
base Fourier coefficient to be nonzero. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderHornExpansion

open Filter Set Metric Complex
open scoped Topology
open Kneser.AllOrderGateFourier Kneser.AllOrderScalarAnalytic Kneser.CauchyHigherTaylor
open Kneser.AllOrderCompactGate Kneser.GateFourierDerivative

def hornReference (n : ℤ) (c d : ℕ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  scalarPolynomial c m z * Complex.exp (-Kneser.fourierFrequency n * scalarPolynomial d m z)

def logReference (n : ℤ) (c d : ℕ → ℂ) (m : ℕ) (z : ℂ) : ℂ :=
  Complex.log (hornReference n c d m z / hornReference n c d m 0)

theorem hornReference_zero (n : ℤ) (c d : ℕ → ℂ) (m : ℕ) :
    hornReference n c d m 0 = c 0 * Complex.exp (-Kneser.fourierFrequency n * d 0) := by
  simp only [hornReference, scalarPolynomial_zero]

theorem hornReference_zero_ne (n : ℤ) (c d : ℕ → ℂ) (m : ℕ) (hc : c 0 ≠ 0) :
    hornReference n c d m 0 ≠ 0 := by
  rw [hornReference_zero]
  exact mul_ne_zero hc (Complex.exp_ne_zero _)

theorem analyticAt_hornReference (n : ℤ) (c d : ℕ → ℂ) (m : ℕ) (z : ℂ) :
    AnalyticAt ℂ (hornReference n c d m) z := by
  exact (analyticAt_scalarPolynomial c m z).mul
    ((analyticAt_const.mul (analyticAt_scalarPolynomial d m z)).cexp)

theorem analyticAt_logReference (n : ℤ) (c d : ℕ → ℂ) (m : ℕ) (hc : c 0 ≠ 0) :
    AnalyticAt ℂ (logReference n c d m) 0 := by
  apply (analyticAt_hornReference n c d m 0).div_const |>.clog
  simp [div_self (hornReference_zero_ne n c d m hc)]

theorem hornReference_first_coefficient (n : ℤ) (c d : ℕ → ℂ) (m : ℕ) (hm : 1 ≤ m) :
    coefficient (hornReference n c d m) 1 =
      Complex.exp (-Kneser.fourierFrequency n * d 0) *
        (c 1 - Kneser.fourierFrequency n * c 0 * d 1) := by
  have hd := Kneser.hasDerivAt_hornCoefficient n (scalarPolynomial c m) (scalarPolynomial d m)
    (c 0) (-d 0) (c 1) (d 1) (scalarPolynomial_zero c m)
    (by simpa using scalarPolynomial_zero d m)
    (scalarPolynomial_hasDerivAt_zero c m hm) (scalarPolynomial_hasDerivAt_zero d m hm)
  simp only [coefficient, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
  change deriv (Kneser.hornCoefficient n (scalarPolynomial c m) (scalarPolynomial d m)) 0 = _
  simpa only [mul_neg, neg_mul] using hd.deriv

theorem logReference_first_coefficient (n : ℤ) (c d : ℕ → ℂ) (m : ℕ)
    (hm : 1 ≤ m) (hc : c 0 ≠ 0) :
    coefficient (logReference n c d m) 1 = 2 * Kneser.hornKappa n (c 0) (c 1) (d 1) := by
  have hd := Kneser.hasDerivAt_log_normalizedHornCoefficient n
    (scalarPolynomial c m) (scalarPolynomial d m) (c 0) (-d 0) (c 1) (d 1)
    (scalarPolynomial_zero c m) (by simpa using scalarPolynomial_zero d m) hc
    (scalarPolynomial_hasDerivAt_zero c m hm) (scalarPolynomial_hasDerivAt_zero d m hm)
  simp only [coefficient, iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, div_one]
  exact hd.deriv

theorem raw_horn_scalarExpansion (n : ℤ) (tn t0 : ℝ → ℂ) (c d : ℕ → ℂ) (m : ℕ)
    (hn : ScalarExpansion tn c m) (h0 : ScalarExpansion t0 d m) :
    ScalarExpansion (Kneser.realHornCoefficient n tn t0)
      (coefficient (hornReference n c d m)) m := by
  let g : ℂ → ℂ × ℂ := fun z => (scalarPolynomial c m z, scalarPolynomial d m z)
  let G : ℂ × ℂ → ℂ := fun p => p.1 * Complex.exp (-Kneser.fourierFrequency n * p.2)
  have hga : AnalyticAt ℂ g 0 :=
    (analyticAt_scalarPolynomial c m 0).prod (analyticAt_scalarPolynomial d m 0)
  have hG : AnalyticAt ℂ G (g 0) :=
    analyticAt_fst.mul ((analyticAt_const.mul analyticAt_snd).cexp)
  obtain ⟨C, hC, he⟩ := scalar_pair_reference tn t0 c d m hn h0
  have hError := analytic_transform_reference (fun s => (tn s, t0 s)) g m C hC hga he G hG
  apply scalarExpansion_of_analytic_reference _ _ m (analyticAt_hornReference n c d m 0)
  · simp only [hornReference_zero, Kneser.realHornCoefficient, hn.1, h0.1]
  · exact hError

theorem log_horn_scalarExpansion (n : ℤ) (tn t0 : ℝ → ℂ) (c d : ℕ → ℂ) (m : ℕ)
    (hn : ScalarExpansion tn c m) (h0 : ScalarExpansion t0 d m) (hB : tn 0 ≠ 0) :
    ScalarExpansion (fun s => Complex.log (Kneser.realNormalizedHornCoefficient n tn t0 s))
      (coefficient (logReference n c d m)) m ∧
    (∀ᶠ s : ℝ in 𝓝[>] 0, Kneser.realNormalizedHornCoefficient n tn t0 s ∈ Complex.slitPlane) ∧
    coefficient (logReference n c d m) 0 = 0 := by
  have hc : c 0 ≠ 0 := by rwa [hn.1]
  let g : ℂ → ℂ × ℂ := fun z => (scalarPolynomial c m z, scalarPolynomial d m z)
  let K : ℂ := Kneser.realHornCoefficient n tn t0 0
  let G : ℂ × ℂ → ℂ := fun p => p.1 * Complex.exp (-Kneser.fourierFrequency n * p.2) / K
  have hK : K ≠ 0 := mul_ne_zero hB (Complex.exp_ne_zero _)
  have hbase : hornReference n c d m 0 = K := by
    simp only [hornReference_zero, K, Kneser.realHornCoefficient, hn.1, h0.1]
  have hga : AnalyticAt ℂ g 0 :=
    (analyticAt_scalarPolynomial c m 0).prod (analyticAt_scalarPolynomial d m 0)
  have hG : AnalyticAt ℂ G (g 0) :=
    (analyticAt_fst.mul ((analyticAt_const.mul analyticAt_snd).cexp)).div_const
  have hG0 : G (g 0) = 1 := by
    change hornReference n c d m 0 / K = 1
    rw [hbase, div_self hK]
  have hlogG : AnalyticAt ℂ (fun p => Complex.log (G p)) (g 0) :=
    hG.clog (by rw [hG0]; exact Complex.one_mem_slitPlane)
  obtain ⟨C, hC, he⟩ := scalar_pair_reference tn t0 c d m hn h0
  have hError := analytic_transform_reference (fun s => (tn s, t0 s)) g m C hC hga he
    (fun p => Complex.log (G p)) hlogG
  have hBranch : ∀ᶠ s : ℝ in 𝓝[>] 0,
      Kneser.realNormalizedHornCoefficient n tn t0 s ∈ Complex.slitPlane := by
    have ht := hG.continuousAt.tendsto.comp (tendsto_of_reference_bound (fun s => (tn s, t0 s))
      g m C hga he)
    have hmem : Complex.slitPlane ∈ 𝓝 (G (g 0)) := by
      rw [hG0]
      exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
    exact ht.eventually hmem
  refine ⟨?_, hBranch, ?_⟩
  · apply scalarExpansion_of_analytic_reference _ _ m (analyticAt_logReference n c d m hc)
    · unfold logReference Kneser.realNormalizedHornCoefficient
      rw [hbase]
    · simpa only [G, K, g, logReference, hornReference, hbase,
        scalarPolynomial_zero, hn.1, h0.1,
        Kneser.realNormalizedHornCoefficient, Kneser.realHornCoefficient] using hError
  · simp [coefficient, logReference, div_self (hornReference_zero_ne n c d m hc)]

theorem gate_horn_all_orders (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ)
    (hpacket : FinitePacket T b m (ball (0 : ℂ) 4))
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) (ball (0 : ℂ) 4)) :
    ∀ n : ℤ,
      ScalarExpansion (Kneser.realHornCoefficient n
        (fun s => gateFourierCoefficient n 0 (T s))
        (fun s => gateFourierCoefficient 0 0 (T s)))
        (coefficient (hornReference n (fourierCoefficient n b) (fourierCoefficient 0 b) m)) m ∧
      (gateFourierCoefficient n 0 (T 0) ≠ 0 →
        ScalarExpansion (fun s => Complex.log (Kneser.realNormalizedHornCoefficient n
          (fun t => gateFourierCoefficient n 0 (T t))
          (fun t => gateFourierCoefficient 0 0 (T t)) s))
          (coefficient (logReference n (fourierCoefficient n b) (fourierCoefficient 0 b) m)) m ∧
        (∀ᶠ s : ℝ in 𝓝[>] 0, Kneser.realNormalizedHornCoefficient n
          (fun t => gateFourierCoefficient n 0 (T t))
          (fun t => gateFourierCoefficient 0 0 (T t)) s ∈ Complex.slitPlane) ∧
        coefficient (logReference n (fourierCoefficient n b) (fourierCoefficient 0 b) m) 0 = 0) := by
  have hf := gateFourier_scalarExpansion T b m hpacket hT
  intro n
  exact ⟨raw_horn_scalarExpansion n _ _ _ _ m (hf n) (hf 0),
    fun hB => log_horn_scalarExpansion n _ _ _ _ m (hf n) (hf 0) hB⟩

end Kneser.AllOrderHornExpansion

end
