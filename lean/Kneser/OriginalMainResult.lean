import Kneser.ActualBaseTetration
import Kneser.PhysicalMainResult

/-! Main endpoint in the original base variable, with the genuine
exponential map and normalization K(0)=1. The same constructed family,
period line, canonical horn, multiplier parameter and explicit orbit
coefficient occur in all clauses. Classical Kneser continuation at
complex bases is not asserted. -/
set_option autoImplicit false
noncomputable section
namespace Kneser.OriginalMainResult
open Filter Set Complex
open Kneser.ActualBaseTetration Kneser.ActualPhysicalSewnCoefficients
open Kneser.ActualSewnAllOrders Kneser.ActualAllOrderUpperHornBaseline
open Kneser.GateFourierDerivative Kneser.AllOrderParameterExpansion
open Kneser.CanonicalUpperHornCharts Kneser.CanonicalBasinExtension
open Kneser.RealNormalizationAnchor
open scoped Topology

theorem original_first_order
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ)
    (hd : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J)
    (n : ℕ) (hn : 1≤n) (hBn : gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖log (normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s /
          normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0) -
        physicalKappa U H A B e Γ N M Yg V n*p s‖≤C*‖p s‖^2 := by
  simpa only [normalized_original_eq_physical] using
    Kneser.PhysicalMainResult.physical_first_order U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn hBn

theorem original_all_orders
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ)
    (hd : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J)
    (n : ℕ) (hn : 1≤n) (hBn : gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0) :
    ∃ a : ℕ → ℂ, a 0=0 ∧ a 1=physicalKappa U H A B e Γ N M Yg V n ∧
      ∀ m : ℕ, ParameterExpansion
        (fun s => log (normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s/
          normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0)) p a m := by
  have hB := (Kneser.MainResult.actual_nonzero_mode_iff_canonical U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd.all_orders n hn).mpr hBn
  obtain ⟨a,ha0,ha1,_hlim,_hbranch,hall⟩ := hd.coefficients n hn hB
  refine ⟨a,ha0,ha1,?_⟩
  intro m
  simpa only [normalized_original_eq_physical] using hall m

theorem original_canonical_baseline
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ)
    (hd : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J)
    (n : ℕ) (hn : 1≤n) :
    normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0 =
      gateFourierCoefficient n (imageCenter Rₛ Yg).im G*
        exp (Kneser.fourierFrequency n*globalAttracting Rₛ normalizationAnchor) := by
  simpa only [normalized_original_eq_physical] using
    Kneser.PhysicalMainResult.physical_canonical_baseline U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn

/-- An unconditional original-variable endpoint: the true exponential
equation, normalization, period integrals and all finite orders come
from one family. Nonvanishing is only required for logarithms. -/
theorem exists_actual_original_first_order_result :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ, ∃ N M M₀ : ℕ,
    ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ, ∃ W : ℝ → Fiber, ∃ J : ℝ → ℕ,
      PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, BaseFiberData A B e Γ Y P₀ s (W s)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ n : ℤ,
        originalCoefficient A B e Γ Y P₀ s (W s) (J s) n=
          gateFourierCoefficient n 0 (actualSewnCoordinate A B e Γ Y P₀ s (W s))) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        p s=(-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).left)*
          Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).right) : ℝ)) ∧
      (∀ n : ℕ, 1≤n →
        normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0 =
          gateFourierCoefficient n (imageCenter Rₛ Yg).im G*
            exp (Kneser.fourierFrequency n*globalAttracting Rₛ normalizationAnchor)) ∧
      (∀ n : ℕ, 1≤n → gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0 →
        ∃ a : ℕ → ℂ, a 0=0 ∧ a 1=physicalKappa U H A B e Γ N M Yg V n ∧
          ∀ m : ℕ, ParameterExpansion
            (fun s => log (normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s/
              normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0)) p a m) ∧
      ∀ n : ℕ, 1≤n → gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0 →
        ∃ C : ℝ, 0≤C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
          ‖log (normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s /
              normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0) -
            physicalKappa U H A B e Γ N M Yg V n*p s‖≤C*‖p s‖^2 := by
  obtain ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,J,hd⟩ :=
    exists_actual_physical_sewn_coefficients
  obtain ⟨hbase,hint,_heq⟩ := base_family_of_physical_coefficients U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd
  refine ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,J,
    hd,hbase,hint,?_,?_,?_,?_⟩
  · exact Kneser.MainResult.actual_sewn_multiplier_parameter U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd.all_orders
  · intro n hn
    exact original_canonical_baseline U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn
  · intro n hn hBn
    exact original_all_orders U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn hBn
  · intro n hn hBn
    exact original_first_order U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn hBn

end Kneser.OriginalMainResult
end
