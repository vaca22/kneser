import Kneser.ActualSewnAllOrders
import Kneser.ActualUpperHornCoefficientIdentification
import Kneser.ActualOrderedParameterIdentification

/-! Reviewable principal result for the constructed actual sewing.
Its true integral coefficients share the canonical upper-horn baseline,
actual multiplier parameter, coherent all-order expansion and explicit
absolute-orbit first correction. Classical Kneser identification is not
encoded as an assumption or inferred from time normalization. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.MainResult

open Filter Set Complex Kneser.CommonQuadraticBaseline
open Kneser.ActualSewnAllOrders Kneser.ActualAllOrderUpperHornBaseline
open Kneser.GateFourierDerivative Kneser.AllOrderGateFourier
open Kneser.AllOrderParameterExpansion Kneser.CanonicalUpperHornCharts
open Kneser.CanonicalBasinExtension Kneser.RealNormalizationAnchor
open scoped Topology

theorem actual_sewn_first_order
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W)
    (n : ℕ) (hn : 1≤n)
    (hB : gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V 0)≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖log (scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n s /
          scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n 0) -
        physicalKappa U H A B e Γ N M Yg V n * p s‖ ≤ C * ‖p s‖^2 := by
  obtain ⟨a,ha0,ha1,_hlim,_hbranch,hall⟩ := hd.coefficients n hn hB
  obtain ⟨C,hC,he⟩ := (hall 1).2
  have hpoly (z : ℂ) : scalarPolynomial a 1 z=physicalKappa U H A B e Γ N M Yg V n*z := by
    simp [scalarPolynomial,Finset.sum_range_succ,ha0,ha1,mul_comm]
  exact ⟨C,hC,by simpa only [hpoly,show (1:ℕ)+1=2 by norm_num] using he⟩

theorem actual_sewn_baseline
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W)
    (n : ℕ) (hn : 1≤n) :
    scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n 0 =
      gateFourierCoefficient n (imageCenter Rₛ Yg).im G *
        exp (Kneser.fourierFrequency n * globalAttracting Rₛ normalizationAnchor) := by
  have hn0 : (n:ℤ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt (by omega : 0<n))
  simpa only [scaledIntegral,ite_true,localHorn,Kneser.realHornCoefficient] using
    Kneser.ActualUpperHornCoefficientIdentification.actual_baseline_nonzero_coefficient
      U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Yg Vold V p r G hd.baseline n hn0

theorem actual_sewn_multiplier_parameter
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W) :
    ∀ᶠ s : ℝ in 𝓝[>] 0,
      p s=(-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).left) *
        Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).right) : ℝ) := by
  filter_upwards [hd.actual_fibers,
    Kneser.ActualOrderedParameterIdentification.actual_baseline_parameter_eq_ordered_multipliers
      U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Yg Vold V p r G hd.baseline] with s hs hp
  exact hp _ _ hs.control.left_neg hs.control.right_pos hs.control.left_fixed hs.control.right_fixed

/-- The nonzero-mode condition is precisely nonvanishing of the true
canonical global horn coefficient, independently of the gate origin. -/
theorem actual_nonzero_mode_iff_canonical
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W)
    (n : ℕ) (hn : 1≤n) :
    gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V 0)≠0 ↔
      gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0 := by
  let C := scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W
  have hg : C n 0≠0 ↔ gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V 0)≠0 := by
    simp [C,scaledIntegral,localHorn,Kneser.realHornCoefficient,exp_ne_zero]
  have hc : C n 0≠0 ↔ gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0 := by
    rw [show C n 0=_ from actual_sewn_baseline U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd n hn]
    simp [exp_ne_zero]
  exact hg.symm.trans hc

/-- An unconditional endpoint: all data and the true sewing are constructed
from the exponential unfolding. The only restriction on a logarithmic
mode is that its actual baseline coefficient is nonzero. -/
theorem exists_actual_sewn_result :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ, ∃ N M M₀ : ℕ,
    ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ, ∃ W : ℝ → Fiber,
      AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        p s=(-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).left) *
          Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).right) : ℝ)) ∧
      (∀ n : ℕ, 1≤n →
        scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n 0 =
          gateFourierCoefficient n (imageCenter Rₛ Yg).im G *
            exp (Kneser.fourierFrequency n * globalAttracting Rₛ normalizationAnchor)) ∧
      ∀ n : ℕ, 1≤n →
        gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V 0)≠0 →
        ∃ C : ℝ, 0≤C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
          ‖log (scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n s /
              scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n 0) -
            physicalKappa U H A B e Γ N M Yg V n * p s‖ ≤ C * ‖p s‖^2 := by
  obtain ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,hd⟩ :=
    exists_actual_sewn_all_orders
  refine ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,hd,?_,?_,?_⟩
  · exact actual_sewn_multiplier_parameter U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd
  · intro n hn
    exact actual_sewn_baseline U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd n hn
  · intro n hn hB
    exact actual_sewn_first_order U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd n hn hB

end Kneser.MainResult
end
