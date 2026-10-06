import Kneser.ActualGluedPhysicalSewing
import Kneser.OriginalMainResult

/-! The same two-sided physical sewing in the original base variable.
The actual open union, entire repelling patch and regular attracting
patch are retained. The genuine period-line Fourier integrals and all
coherent parameter coefficients use exactly the previously selected
physical family; no classical continuation identity is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.GluedOriginalResult

open Filter Set Metric Complex
open Kneser.ActualSewnAllOrders Kneser.ActualPhysicalSewnCoefficients
open Kneser.ActualFiberKoenigsUniformization Kneser.ActualBaseTetration
open Kneser.ActualGluedPhysicalSewing Kneser.OriginalMainResult
open Kneser.CommonQuadraticBaseline Kneser.ActualAllOrderUpperHornBaseline
open Kneser.GateFourierDerivative Kneser.AllOrderParameterExpansion
open Kneser.CanonicalUpperHornCharts Kneser.CanonicalBasinExtension
open Kneser.RealNormalizationAnchor
open scoped Topology Interval

def gluedOriginal (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  originalCoordinate (gluedFunction A B e Γ Y P₀ s w S z)

structure GluedBaseFiberData (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ) : Prop where
  physical : GluedPhysicalData A B e Γ Y P₀ s w S
  domain_open : IsOpen (gluedDomain A B e Γ Y P₀ s w)
  zero_mem : (0:ℂ)∈gluedDomain A B e Γ Y P₀ s w
  analytic : AnalyticOnNhd ℂ (gluedOriginal A B e Γ Y P₀ s w S) (gluedDomain A B e Γ Y P₀ s w)
  normalized : gluedOriginal A B e Γ Y P₀ s w S 0=1
  tetration : ∀z∈gluedDomain A B e Γ Y P₀ s w,
    z+1∈gluedDomain A B e Γ Y P₀ s w ∧
      gluedOriginal A B e Γ Y P₀ s w S (z+1)=originalExponential s (gluedOriginal A B e Γ Y P₀ s w S z)
  upper_eq : ∀z∈physicalDomain A B e Γ Y P₀ s w,
    gluedOriginal A B e Γ Y P₀ s w S z=originalK A B e Γ Y P₀ s w z
  lower_eq : ∀z∈lowerTimeSource A B e Γ Y P₀ s w,
    gluedOriginal A B e Γ Y P₀ s w S z=originalCoordinate (S (lowerTime A B e Γ Y P₀ s w z))

theorem glued_base_fiber_of_data (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ)
    (hd : GluedPhysicalData A B e Γ Y P₀ s w S) :
    GluedBaseFiberData A B e Γ Y P₀ s w S := by
  refine ⟨hd,hd.domain_open,hd.zero_mem,?_,?_,?_,?_,?_⟩
  · intro z hz
    exact analyticAt_const.mul (analyticAt_const.add (hd.analytic z hz))
  · unfold gluedOriginal
    rw [hd.normalized]
    exact original_anchor
  · intro z hz
    obtain ⟨hz1,he⟩ := hd.abel z hz
    refine ⟨hz1,?_⟩
    unfold gluedOriginal
    rw [he,actual_affine_conjugacy]
  · intro z hz
    unfold gluedOriginal originalK
    rw [hd.upper_eq z hz]
  · intro z hz
    unfold gluedOriginal
    rw [hd.lower_eq z hz]

def gluedOriginalCoefficient (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ) (J : ℕ) (n : ℤ) : ℂ :=
  ∫x : ℝ in (0:ℝ)..1,
    (originalAbelLift s w.left (gluedOriginal A B e Γ Y P₀ s w S ((J:ℂ)+(x:ℂ)))-((J:ℂ)+(x:ℂ)))*
      exp (-Kneser.fourierFrequency n*((J:ℂ)+(x:ℂ)))

theorem glued_original_period_line (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ) (J : ℕ)
    (hg : GluedPhysicalData A B e Γ Y P₀ s w S)
    (hl : PeriodLineData A B e Γ Y P₀ s w J) :
    (∀x∈Icc (0:ℝ) 1, (J:ℂ)+(x:ℂ)∈gluedDomain A B e Γ Y P₀ s w ∧
      originalAbelLift s w.left (gluedOriginal A B e Γ Y P₀ s w S ((J:ℂ)+(x:ℂ)))=
        actualSewnCoordinate A B e Γ Y P₀ s w ((J:ℂ)+(x:ℂ))) ∧
    ∀n : ℤ, gluedOriginalCoefficient A B e Γ Y P₀ s w S J n=
      originalCoefficient A B e Γ Y P₀ s w J n := by
  have hb := glued_base_fiber_of_data A B e Γ Y P₀ s w S hg
  refine ⟨?_,?_⟩
  · intro x hx
    refine ⟨Or.inl (hl.actual_domain x hx),?_⟩
    rw [hb.upper_eq _ (hl.actual_domain x hx)]
    exact (original_period_line_of_data A B e Γ Y P₀ s w J hl).1 x hx |>.2
  · intro n
    unfold gluedOriginalCoefficient originalCoefficient
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x∈Icc (0:ℝ) 1 := by
      simpa only [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
    dsimp only
    rw [hb.upper_eq _ (hl.actual_domain x hx')]

def normalizedGluedCoefficient (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y P₀ : ℝ) (W : ℝ → Fiber) (S : ℝ → ℂ → ℂ) (J : ℝ → ℕ)
    (n : ℕ) (s : ℝ) : ℂ :=
  if s=0 then localHorn T n 0 else
    gluedOriginalCoefficient A B e Γ Y P₀ s (W s) (S s) (J s) n/(scale W s:ℂ)^n

theorem normalized_glued_zero (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y P₀ : ℝ) (W : ℝ → Fiber) (S : ℝ → ℂ → ℂ) (J : ℝ → ℕ) (n : ℕ) :
    normalizedGluedCoefficient A B e Γ T Y P₀ W S J n 0=
      normalizedOriginalCoefficient A B e Γ T Y P₀ W J n 0 := by
  simp only [normalizedGluedCoefficient,normalizedOriginalCoefficient,ite_true]

structure GluedResultData (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ) (S : ℝ → ℂ → ℂ) : Prop where
  physical_coefficients : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J
  glued : ∀ᶠs : ℝ in 𝓝[>] 0, GluedBaseFiberData A B e Γ Y P₀ s (W s) (S s)
  actual_line : ∀ᶠs : ℝ in 𝓝[>] 0, ∀x∈Icc (0:ℝ) 1,
    (J s:ℂ)+(x:ℂ)∈gluedDomain A B e Γ Y P₀ s (W s) ∧
      originalAbelLift s (W s).left (gluedOriginal A B e Γ Y P₀ s (W s) (S s) ((J s:ℂ)+(x:ℂ)))=
        actualSewnCoordinate A B e Γ Y P₀ s (W s) ((J s:ℂ)+(x:ℂ))
  actual_coefficients : ∀ᶠs : ℝ in 𝓝[>] 0, ∀n : ℤ,
    gluedOriginalCoefficient A B e Γ Y P₀ s (W s) (S s) (J s) n=
      gateFourierCoefficient n 0 (actualSewnCoordinate A B e Γ Y P₀ s (W s))
  actual_multiplier_parameter : ∀ᶠs : ℝ in 𝓝[>] 0,
    p s=(-Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).left)*
      Real.log (Kneser.PositiveKoenigsOrbit.multiplier s (W s).right):ℝ)
  canonical_baseline : ∀n : ℕ, 1≤n →
    normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n 0=
      gateFourierCoefficient n (imageCenter Rₛ Yg).im G*
        exp (Kneser.fourierFrequency n*globalAttracting Rₛ normalizationAnchor)
  coefficients : ∀n : ℕ, 1≤n → gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0 →
    ∃a : ℕ → ℂ, a 0=0 ∧ a 1=physicalKappa U H A B e Γ N M Yg V n ∧
      Tendsto (normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n)
        (𝓝[>] 0) (𝓝 (localHorn (actualTransition U H A B e Γ N M Yg V) n 0)) ∧
      (∀ᶠs : ℝ in 𝓝[>] 0,
        normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n s/
          normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n 0∈slitPlane) ∧
      ∀m : ℕ, ParameterExpansion
        (fun s => log (normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n s/
          normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n 0)) p a m
  first_order : ∀n : ℕ, 1≤n → gateFourierCoefficient n (imageCenter Rₛ Yg).im G≠0 →
    ∃C : ℝ, 0≤C ∧ ∀ᶠs : ℝ in 𝓝[>] 0,
      ‖log (normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n s/
          normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n 0)-
        physicalKappa U H A B e Γ N M Yg V n*p s‖≤C*‖p s‖^2

theorem glued_result_of_physical_coefficients
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ)
    (hd : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J) :
    ∃S : ℝ → ℂ → ℂ, GluedResultData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀
      N M M₀ Vold V p r G W J S := by
  obtain ⟨S,hS⟩ := glued_family_of_physical_coefficients U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd
  have heq : ∀ᶠs : ℝ in 𝓝[>] 0, ∀n : ℕ,
      normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n s=
        normalizedOriginalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s := by
    filter_upwards [hS,hd.actual_line] with s hs hl
    intro n
    simp only [normalizedGluedCoefficient,normalizedOriginalCoefficient,
      (glued_original_period_line A B e Γ Y P₀ s (W s) (S s) (J s) hs hl).2 n]
  refine ⟨S,hd,hS.mono (fun s hs => glued_base_fiber_of_data A B e Γ Y P₀ s (W s) (S s) hs),?_,?_,?_,?_,?_,?_⟩
  · filter_upwards [hS,hd.actual_line] with s hs hl
    exact (glued_original_period_line A B e Γ Y P₀ s (W s) (S s) (J s) hs hl).1
  · filter_upwards [hS,hd.actual_line] with s hs hl
    intro n
    exact ((glued_original_period_line A B e Γ Y P₀ s (W s) (S s) (J s) hs hl).2 n).trans
      ((original_period_line_of_data A B e Γ Y P₀ s (W s) (J s) hl).2 n)
  · exact Kneser.MainResult.actual_sewn_multiplier_parameter U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd.all_orders
  · intro n hn
    rw [normalized_glued_zero]
    exact original_canonical_baseline U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn
  · intro n hn hBn
    have hB := (Kneser.MainResult.actual_nonzero_mode_iff_canonical U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd.all_orders n hn).mpr hBn
    obtain ⟨a,ha0,ha1,ht,hslit,hall⟩ := hd.coefficients n hn hB
    let f := normalizedGluedCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W S J n
    let g := normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n
    have hfg : f=ᶠ[𝓝[>] 0]g := by
      filter_upwards [heq] with s hs
      exact (hs n).trans (congrFun (normalized_original_eq_physical A B e Γ _ Y P₀ W J n) s)
    have hfg0 : f 0=g 0 := by
      exact (normalized_glued_zero A B e Γ _ Y P₀ W S J n).trans
        (congrFun (normalized_original_eq_physical A B e Γ _ Y P₀ W J n) 0)
    refine ⟨a,ha0,ha1,ht.congr' hfg.symm,?_,?_⟩
    · filter_upwards [hfg,hslit] with s hs hslit
      change f s/f 0∈slitPlane
      rw [hs,hfg0]
      exact hslit
    · intro m
      change ParameterExpansion (fun s => log (f s/f 0)) p a m
      exact parameterExpansion_of_eventuallyEq (fun s => log (f s/f 0))
        (fun s => log (g s/g 0)) p a m (by rw [hfg0])
          (hfg.mono (fun s hs => by
            change log (f s/f 0)=log (g s/g 0)
            rw [hs,hfg0])) (hall m)
  · intro n hn hBn
    obtain ⟨C,hC,hb⟩ := original_first_order U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd n hn hBn
    refine ⟨C,hC,?_⟩
    filter_upwards [heq,hb] with s hs hb
    simpa only [hs n,normalized_glued_zero] using hb

theorem exists_actual_glued_original_result :
    ∃U H A B : ℂ → ℂ, ∃K : ℂ → ℂ → ℂ, ∃F : ℂ × ℂ → ℂ,
    ∃e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃Γ : ℕ → ℂ × ℂ → ℂ,
    ∃R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ, ∃N M M₀ : ℕ,
    ∃Vold V : ℝ → ℂ → ℂ, ∃p r G : ℂ → ℂ, ∃W : ℝ → Fiber, ∃J : ℝ → ℕ, ∃S : ℝ → ℂ → ℂ,
      GluedResultData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J S := by
  obtain ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,J,hd⟩ :=
    exists_actual_physical_sewn_coefficients
  obtain ⟨S,hS⟩ := glued_result_of_physical_coefficients U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J hd
  exact ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,J,S,hS⟩

end Kneser.GluedOriginalResult
end
