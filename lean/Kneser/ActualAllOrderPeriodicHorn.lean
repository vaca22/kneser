import Kneser.ActualRealNormalizedPeriodicity
import Kneser.AllOrderPeriodicPacket
import Kneser.ActualAllOrderHornParameter

/-! A single actual real-normalized transition carries the complete
integer-order packets, genuine periodic strip continuation, multiplier
parameter and one coherent sequence of horn logarithm coefficients. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualAllOrderPeriodicHorn

open Filter Set Metric Kneser.CommonQuadraticBaseline
open Kneser.ActualQuantitativeGateTransition Kneser.ActualCenteredGatePacket
open Kneser.AllOrderSingleInverse Kneser.AllOrderCompactGate
open Kneser.ActualRealNormalizedTransition Kneser.ActualAllOrderHornParameter
open Kneser.LocalPeriodicStrip Kneser.AllOrderPeriodicPacket
open scoped Topology

theorem finitePacket_zero_analytic (T : ℝ → ℂ → ℂ) (b : ℕ → ℂ → ℂ) (m : ℕ)
    (hb : FinitePacket T b m (ball (0 : ℂ) 3)) : AnalyticOnNhd ℂ (T 0) (ball (0 : ℂ) 3) := by
  intro z hz
  apply (hb.1 0 (Nat.zero_le m) z hz).congr
  have hn : ∀ᶠ w in 𝓝 z, w ∈ ball (0 : ℂ) 3 := isOpen_ball.mem_nhds hz
  exact hn.mono (fun w hw => hb.2.1 w hw)

theorem logarithm_lift_eq (T : ℝ → ℂ → ℂ) (n : ℤ) (s : ℝ) :
    logarithm (fun t => lift (T t)) n s = logarithm T n s := by
  unfold logarithm Kneser.realNormalizedHornCoefficient Kneser.realHornCoefficient
  simp only [gateFourier_zero_lift_eq]

theorem exists_actual_all_order_periodic_horn :
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
      CoherentHornData (transition U H A B e Γ N M Y V) p r ∧
      AnalyticOnNhd ℂ (lift (transition U H A B e Γ N M Y V 0)) strip ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (lift (transition U H A B e Γ N M Y V s)) strip) ∧
      ∀ m : ℕ, 1 ≤ m → ∃ b : ℕ → ℂ → ℂ,
        FinitePacket (transition U H A B e Γ N M Y V) b m (ball (0 : ℂ) 3) ∧
        FinitePacket (fun s => lift (transition U H A B e Γ N M Y V s)) (stripCoefficient b) m strip := by
  obtain ⟨U,H,A,B,K,F,e,Γ,R,N,M,M₀,Y,Vold,V,hdata,_hprep,hR,hlocal,_hdeep,_hab,_hentry,ht,hv,hT,hpack⟩ :=
    exists_actual_real_normalized_transition_with_data
  have hperiod := Kneser.ActualRealNormalizedPeriodicity.eventually_transition_translation
    U H A B e Γ R N M M₀ Y Vold V ht hR hlocal hv
  have hperiod0 := Kneser.ActualRealNormalizedPeriodicity.transition_zero_translation
    U H A B e Γ R N M M₀ Y Vold V ht hR hlocal hv
  obtain ⟨b₁,hb₁⟩ := hpack 1 le_rfl
  have hT0 := finitePacket_zero_analytic _ b₁ 1 hb₁
  obtain ⟨p,hpa,hp0,hpd,hprod⟩ :=
    Kneser.ActualCommonMultiplierParameter.exists_parameter_of_actual_data
      U H (first (e 1)) (second (e 1)) A B K F (Γ 1) hdata
  obtain ⟨r,hra,hr0,hrd,hl,hright,hcoh⟩ := coherent_horn_data_of_actual_packets _ p hpack hT hpa hp0 hpd
  refine ⟨U,H,A,B,K,F,e,Γ,R,N,M,M₀,Y,Vold,V,p,r,hdata,ht,hv,hpa,hp0,hpd,hprod,
    hra,hr0,hrd,hl,hright,hcoh,lift_analytic_of_ball_three _ hT0 hperiod0,?_,?_⟩
  · filter_upwards [hT,hperiod] with s hs hp
    exact lift_analytic_of_ball_three _ hs hp
  · intro m hm
    obtain ⟨b,hb⟩ := hpack m hm
    exact ⟨b,hb,finitePacket_lift _ b m hb hperiod⟩

end Kneser.ActualAllOrderPeriodicHorn
