import Kneser.ActualPhysicalSewnCoefficients
import Kneser.MainResult
import Kneser.ActualSewnModeRatios
import Kneser.ActualEntireRepellingCoordinate

/-! Principal theorem for the genuine physical sewing of the actual
exponential unfolding. The coefficients are integrals of its true
Koenigs Abel lift on a proved period line. Their first correction is
the explicit absolute-orbit formula, and their baseline is the true
canonical global horn. All actual data are constructed unconditionally.
This is not an identification with separately defined classical Kneser
continuation at complex bases. -/
set_option autoImplicit false
noncomputable section
namespace Kneser.PhysicalMainResult
open Filter Set Complex
open Kneser.ActualPhysicalSewnCoefficients Kneser.ActualSewnAllOrders
open Kneser.ActualAllOrderUpperHornBaseline Kneser.GateFourierDerivative
open Kneser.AllOrderGateFourier Kneser.AllOrderParameterExpansion
open Kneser.CanonicalUpperHornCharts Kneser.CanonicalBasinExtension
open Kneser.RealNormalizationAnchor
open scoped Topology

theorem physical_first_order
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ)
    (hd : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J)
    (n : ℕ) (hn : 1≤n) (hBn : gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖log (normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s /
          normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0) -
        physicalKappa U H A B e Γ N M Yg V n*p s‖≤C*‖p s‖^2 := by
  have hB := (Kneser.MainResult.actual_nonzero_mode_iff_canonical U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd.all_orders n hn).mpr hBn
  obtain ⟨a,ha0,ha1,_hlim,_hbranch,hall⟩ := hd.coefficients n hn hB
  obtain ⟨C,hC,he⟩ := (hall 1).2
  have hpoly (z : ℂ) : scalarPolynomial a 1 z=physicalKappa U H A B e Γ N M Yg V n*z := by
    simp [scalarPolynomial,Finset.sum_range_succ,ha0,ha1,mul_comm]
  exact ⟨C,hC,by simpa only [hpoly,show (1:ℕ)+1=2 by norm_num] using he⟩

theorem physical_canonical_baseline
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ)
    (hd : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J)
    (n : ℕ) (hn : 1≤n) :
    normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0 =
      gateFourierCoefficient n (imageCenter Rₛ Yg).im G*
        exp (Kneser.fourierFrequency n*globalAttracting Rₛ normalizationAnchor) := by
  simpa only [normalizedPhysicalCoefficient,scaledIntegral,ite_true] using
    Kneser.MainResult.actual_sewn_baseline U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀
      N M M₀ Vold V p r G W hd.all_orders n hn

/-- No analytic coordinates, convergence, decay, welding comparison,
parameter identification or physical coefficient identity are inputs.
The nonzero condition is on the actual canonical upper horn. -/
theorem exists_actual_physical_first_order_result :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ, ∃ N M M₀ : ℕ,
    ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ, ∃ W : ℝ → Fiber, ∃ J : ℝ → ℕ,
      PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        p s=(-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).left)*
          Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).right) : ℝ)) ∧
      (∀ n : ℕ, 1≤n →
        normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0 =
          gateFourierCoefficient n (imageCenter Rₛ Yg).im G*
            exp (Kneser.fourierFrequency n*globalAttracting Rₛ normalizationAnchor)) ∧
      ∀ n : ℕ, 1≤n → gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0 →
        ∃ C : ℝ, 0≤C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
          ‖log (normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s /
              normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0) -
            physicalKappa U H A B e Γ N M Yg V n*p s‖≤C*‖p s‖^2 := by
  obtain ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,J,hd⟩ :=
    exists_actual_physical_sewn_coefficients
  refine ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,J,hd,?_,?_,?_⟩
  · exact Kneser.MainResult.actual_sewn_multiplier_parameter U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀
      N M M₀ Vold V p r G W hd.all_orders
  · intro n hn
    exact physical_canonical_baseline U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn
  · intro n hn hBn
    exact physical_first_order U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn hBn

end Kneser.PhysicalMainResult
end
