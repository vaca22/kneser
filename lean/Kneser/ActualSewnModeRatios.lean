import Kneser.MainResult
import Kneser.ParameterModeRatios

/-! All-order expansion of the true sewn Fourier mode ratios. Lambda
cancels exactly in c_n/c_1^n, and the mean-mode contribution cancels
from its explicit first correction. -/
set_option autoImplicit false
noncomputable section
namespace Kneser.ActualSewnModeRatios
open Filter Set Complex
open Kneser.ActualSewnAllOrders Kneser.CommonQuadraticBaseline
open Kneser.ActualAllOrderUpperHornBaseline Kneser.ActualRealNormalizedFirstCoefficient
open Kneser.GateFourierDerivative Kneser.AllOrderParameterExpansion
open Kneser.ParameterModeRatios
open scoped Topology

theorem physicalKappa_ratio (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N M : ℕ) (Yg : ℝ) (V : ℝ → ℂ → ℂ) (n : ℕ) :
    physicalKappa U H A B e Γ N M Yg V n-(n:ℂ)*physicalKappa U H A B e Γ N M Yg V 1 =
      gateCorrectionCoefficient n 0 (physicalCorrection U H A B e Γ N M Yg V) /
        (2*gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V 0)) -
      (n:ℂ)*gateCorrectionCoefficient 1 0 (physicalCorrection U H A B e Γ N M Yg V) /
        (2*gateFourierCoefficient 1 0 (actualTransition U H A B e Γ N M Yg V 0)) := by
  simp only [physicalKappa,Kneser.hornKappa,Int.cast_natCast,Int.cast_one]
  ring

/-- The exponentially small scale cancels in a true mode ratio. This
uses the actual integral coefficients of the same selected fiber. -/
theorem scaled_ratio_eq_integral_ratio (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y P₀ : ℝ) (W : ℝ → Fiber) (n : ℕ) (s : ℝ)
    (hs : s≠0) (hΛ : (scale W s:ℂ)≠0)
    (hc : gateFourierCoefficient 1 0 (actualSewnCoordinate A B e Γ Y P₀ s (W s))≠0) :
    scaledIntegral A B e Γ T Y P₀ W n s/(scaledIntegral A B e Γ T Y P₀ W 1 s)^n =
      gateFourierCoefficient n 0 (actualSewnCoordinate A B e Γ Y P₀ s (W s)) /
        (gateFourierCoefficient 1 0 (actualSewnCoordinate A B e Γ Y P₀ s (W s)))^n := by
  simp only [scaledIntegral,ite_eq_right hs,pow_one,div_pow,Nat.cast_one]
  field_simp [hΛ,hc]

theorem actual_sewn_mode_ratio_all_orders
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W)
    (n : ℕ) (hn : 1≤n)
    (hBn : gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V 0)≠0)
    (hB1 : gateFourierCoefficient 1 0 (actualTransition U H A B e Γ N M Yg V 0)≠0) :
    let C := scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W
    ∃ a : ℕ → ℂ, a 0=0 ∧
      a 1=physicalKappa U H A B e Γ N M Yg V n-(n:ℂ)*physicalKappa U H A B e Γ N M Yg V 1 ∧
      ∀ m : ℕ, ParameterExpansion
        (fun s => log ((C n s/C n 0)/(C 1 s/C 1 0)^n)) p a m := by
  let C := scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W
  obtain ⟨an,han0,han1,hln,_hbn,han⟩ := hd.coefficients n hn hBn
  obtain ⟨a1,ha10,ha11,hl1,_hb1,ha1⟩ := hd.coefficients 1 le_rfl hB1
  have hCn : C n 0≠0 := by
    simp only [C,scaledIntegral,ite_true]
    exact mul_ne_zero hBn (exp_ne_zero _)
  have hC1 : C 1 0≠0 := by
    simp only [C,scaledIntegral,ite_true,Nat.cast_one]
    exact mul_ne_zero hB1 (exp_ne_zero _)
  have hlimn : Tendsto (C n) (𝓝[>] 0) (𝓝 (C n 0)) := by
    simpa only [C,scaledIntegral,ite_true] using hln
  have hlim1 : Tendsto (C 1) (𝓝[>] 0) (𝓝 (C 1 0)) := by
    simpa only [C,scaledIntegral,ite_true] using hl1
  refine ⟨fun j => an j-(n:ℂ)*a1 j,?_,?_,?_⟩
  · simp only [han0,ha10,mul_zero,sub_zero]
  · simp only [han1,ha11,Nat.cast_one]
  · exact all_orders_normalized_ratio (C n) (C 1) p an a1 n hCn hC1 hlimn hlim1 han ha1

end Kneser.ActualSewnModeRatios
end
