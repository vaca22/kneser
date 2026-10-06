import Kneser.ActualRealNormalizedTransition
import Kneser.ActualCommonMultiplierParameter
import Kneser.AllOrderGateExtraction
import Kneser.AllOrderParameterCoherence

/-! One all-orders sequence for the actual real-anchor normalized horn
logarithm, in the multiplier parameter of the SAME preparation roots.
Every finite coefficient is identified with the genuine Fourier integrals
and finite analytic exp/log/inverse-parameter reference. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualAllOrderHornParameter

open Filter Set Metric Kneser.AllOrderCompactGate Kneser.AllOrderGateFourier
open Kneser.AllOrderGateExtraction Kneser.AllOrderHornExpansion
open Kneser.AllOrderParameterExpansion Kneser.AllOrderParameterCoherence
open Kneser.GateFourierDerivative Kneser.ActualRealNormalizedTransition
open Kneser.CommonQuadraticBaseline Kneser.ActualQuantitativeGateTransition
open Kneser.ActualCenteredGatePacket Kneser.AllOrderSingleInverse
open scoped Topology

def logarithm (T : ℝ → ℂ → ℂ) (n : ℤ) (s : ℝ) : ℂ :=
  Complex.log (Kneser.realNormalizedHornCoefficient n
    (fun t => gateFourierCoefficient n 0 (T t))
    (fun t => gateFourierCoefficient 0 0 (T t)) s)

def explicitCoefficient (n : ℤ) (b : ℕ → ℂ → ℂ) (m : ℕ) (r : ℂ → ℂ) (j : ℕ) : ℂ :=
  Kneser.CauchyHigherTaylor.coefficient
    (parameterReference (Kneser.CauchyHigherTaylor.coefficient
      (logReference n (fourierCoefficient n b) (fourierCoefficient 0 b) m)) m r) j

def CoherentHornData (T : ℝ → ℂ → ℂ) (p r : ℂ → ℂ) : Prop :=
  ∀ n : ℤ, gateFourierCoefficient n 0 (T 0) ≠ 0 →
    ∃ a : ℕ → ℂ, a 0 = 0 ∧
      (∀ m : ℕ, ParameterExpansion (logarithm T n) p a m) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, Kneser.realNormalizedHornCoefficient n
        (fun t => gateFourierCoefficient n 0 (T t))
        (fun t => gateFourierCoefficient 0 0 (T t)) s ∈ Complex.slitPlane) ∧
      ∀ m : ℕ, 1 ≤ m → ∃ b : ℕ → ℂ → ℂ,
        FinitePacket T b m (ball (0 : ℂ) 3) ∧ ∀ j ≤ m, a j = explicitCoefficient n b m r j

theorem coherent_horn_data_of_actual_packets (T : ℝ → ℂ → ℂ) (p : ℂ → ℂ)
    (hpacket : ∀ m : ℕ, 1 ≤ m → ∃ b : ℕ → ℂ → ℂ, FinitePacket T b m (ball (0 : ℂ) 3))
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (T s) (ball (0 : ℂ) 3))
    (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r 0 ∧ r 0 = 0 ∧ HasDerivAt r (1 / 2) 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, r (p z) = z) ∧ (∀ᶠ z : ℂ in 𝓝 0, p (r z) = z) ∧
      CoherentHornData T p r := by
  obtain ⟨r, hra, hr0, hrd, hl, hright, htransfer⟩ := exists_parameter_expansions p hpa hp0 hp
  refine ⟨r, hra, hr0, hrd, hl, hright, ?_⟩
  intro n hB
  have hfinite (m : ℕ) (hm : 1 ≤ m) : ∃ b : ℕ → ℂ → ℂ,
      FinitePacket T b m (ball (0 : ℂ) 3) ∧
      ParameterExpansion (logarithm T n) p (explicitCoefficient n b m r) m ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, Kneser.realNormalizedHornCoefficient n
        (fun t => gateFourierCoefficient n 0 (T t))
        (fun t => gateFourierCoefficient 0 0 (T t)) s ∈ Complex.slitPlane) := by
    obtain ⟨b, hb⟩ := hpacket m hm
    have hh := (gate_horn_all_orders_of_set T b m (ball (0 : ℂ) 3)
      real_gate_mem_ball_three hb hT n).2 hB
    exact ⟨b, hb, htransfer _ _ m hh.1, hh.2.1⟩
  obtain ⟨a, ha⟩ := exists_coherent_positive_parameter_orders (logarithm T n) p hpa hp0 hp
    (fun m hm => by obtain ⟨b, _hb, hf, _hbranch⟩ := hfinite m hm; exact ⟨_, hf⟩)
  obtain ⟨_b₁, _hb₁, _hf₁, hbranch⟩ := hfinite 1 le_rfl
  have hzero : logarithm T n 0 = 0 := by
    unfold logarithm Kneser.realNormalizedHornCoefficient Kneser.realHornCoefficient
    rw [div_self (mul_ne_zero hB (Complex.exp_ne_zero _))]
    exact Complex.log_one
  refine ⟨a, (ha 0).1.trans hzero, ha, hbranch, ?_⟩
  intro m hm
  obtain ⟨b, hb, hf, _hbranch⟩ := hfinite m hm
  exact ⟨b, hb, parameterExpansion_unique hpa hp0 hp (ha m) hf⟩

/-- All analytic, orbit, inverse and normalization data of this endpoint
are constructed for the exponential unfolding.  The same p uses the
actual preparation multiplier roots, rather than independent cusp data. -/
theorem exists_actual_coherent_horn_parameter_expansion :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2 * n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R : ℝ, ∃ N M M₀ : ℕ, ∃ Y : ℝ, ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r : ℂ → ℂ,
      Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData
        U H (first (e 1)) (second (e 1)) A B K F (Γ 1) ∧
      ActualTransitionData U H (first (e 1)) (second (e 1)) A B (Γ 1) R N M₀ Y Vold ∧
      InverseData (centeredRepelling U H (first (e 1)) (second (e 1)) A B (Γ 1) N Y) V 12 ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      (∀ x : ℂ, p (x ^ 2) = -Complex.log (Kneser.ExponentialPreparedModel.rootMultiplier U x) *
        Complex.log (Kneser.ExponentialPreparedModel.rootMultiplier U (-x))) ∧
      AnalyticAt ℂ r 0 ∧ r 0 = 0 ∧ HasDerivAt r (1 / 2) 0 ∧
      (∀ᶠ z : ℂ in 𝓝 0, r (p z) = z) ∧ (∀ᶠ z : ℂ in 𝓝 0, p (r z) = z) ∧
      CoherentHornData (transition U H A B e Γ N M Y V) p r := by
  obtain ⟨U, H, A, B, K, F, e, Γ, R, N, M, M₀, Y, Vold, V, hdata, ht, hv, hT, hpacket⟩ :=
    exists_actual_real_normalized_transition_all_orders
  obtain ⟨p, hpa, hp0, hpd, hproduct⟩ :=
    Kneser.ActualCommonMultiplierParameter.exists_parameter_of_actual_data
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  obtain ⟨r, hra, hr0, hrd, hl, hright, hhorn⟩ := coherent_horn_data_of_actual_packets _ p hpacket hT hpa hp0 hpd
  exact ⟨U, H, A, B, K, F, e, Γ, R, N, M, M₀, Y, Vold, V, p, r, hdata, ht, hv,
    hpa, hp0, hpd, hproduct, hra, hr0, hrd, hl, hright, hhorn⟩

end Kneser.ActualAllOrderHornParameter
