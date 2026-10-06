import Kneser.ActualFiberKoenigsUniformization
import Kneser.ActualRegularTimeLift

/-! The Fourier integrals of the selected sewing are exactly the
integrals of the genuine physical function's principal Koenigs Abel
lift on one proved right period line. The same family therefore has
the same coherent multiplier-parameter expansions and explicit first
orbit-series correction. No classical Kneser identification is assumed. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.ActualPhysicalSewnCoefficients

open Filter Set Metric Complex
open Kneser.ActualSewnAllOrders Kneser.ActualFiberKoenigsUniformization
open Kneser.ActualRegularTimeLift Kneser.ActualRegularKoenigsInverse
open Kneser.ActualHolomorphicGrowingLens Kneser.GrowingBandGeometry
open Kneser.ActualNormalizedGrowingTransition Kneser.NormalizedGrowingFourier
open Kneser.FourierSewing Kneser.WeightedFourier Kneser.GateFourierDerivative
open Kneser.PositiveKoenigsOrbit Kneser.ActualKoenigsGlobalRealPhase
open Kneser.CommonQuadraticBaseline Kneser.RealNormalizationAnchor
open Kneser.ActualAllOrderUpperHornBaseline Kneser.AllOrderParameterExpansion
open scoped Topology Interval

def physicalCoefficient (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (J : ℕ) (n : ℤ) : ℂ :=
  ∫ x : ℝ in (0:ℝ)..1,
    (principalKoenigsLift s w.left realAnchor
      (physicalFunction A B e Γ Y P₀ s w ((J:ℂ)+(x:ℂ))) - ((J:ℂ)+(x:ℂ))) *
        exp (-Kneser.fourierFrequency n*((J:ℂ)+(x:ℂ)))

structure PeriodLineData (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (J : ℕ) : Prop where
  actual_domain : ∀ x ∈ Icc (0:ℝ) 1,
    (J:ℂ)+(x:ℂ) ∈ physicalDomain A B e Γ Y P₀ s w
  exact_lift : ∀ x ∈ Icc (0:ℝ) 1,
    principalKoenigsLift s w.left realAnchor
      (physicalFunction A B e Γ Y P₀ s w ((J:ℂ)+(x:ℂ))) =
        actualSewnCoordinate A B e Γ Y P₀ s w ((J:ℂ)+(x:ℂ))
  coefficient : ∀ n : ℤ, physicalCoefficient A B e Γ Y P₀ s w J n =
    gateFourierCoefficient n 0 (actualSewnCoordinate A B e Γ Y P₀ s w)

theorem exists_period_line_of_fiber_data (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y η Mg P₀ s : ℝ) (w : Fiber)
    (hd : FiberData A B e Γ T Y η Mg P₀ s w) (hs : 0<s) (hs1 : s<1)
    (hH : 3<sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) :
    ∃ J : ℕ, PeriodLineData A B e Γ Y P₀ s w J := by
  have hc := hd.control
  have hphys := physical_data_of_fiber_data A B e Γ T Y η Mg P₀ s w hd hs hs1 hH
  have ha := real_root_gt_neg_one s w.left hc.left_fixed
  have hμ : 0<multiplier s w.left := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s w.left<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hr := actual_anchor_left_of_control (first (e 1)) (second (e 1)) A B (Γ 1)
    s w.left w.right w.theta Y η Mg P₀ hc
  have hanchor : -1<realAnchor := by unfold realAnchor; linarith [Real.exp_pos (-1)]
  have hdist : w.left-realAnchor<1 := by linarith [hc.left_neg]
  have hlog : |Real.log (multiplier s w.left)|≤1 := by
    rw [abs_of_neg (Real.log_neg hμ hμ1),←hc.theta_actual]
    nlinarith [hc.width,hc.height_large,Real.pi_lt_four,hc.theta_pos]
  let H := sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1
  let t₀ := gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)
  have hz₀ : centerPoint A B e Γ s w ∈ upperSource H := by
    simpa only [timeSource,mem_ofPred_eq,add_zero] using hphys.zero_mem.1
  have hgap : 0≤H+(normalizingCentre (height w.theta) t₀+w.shift).im := by
    change 1-H<(normalizingCentre (height w.theta) t₀+w.shift).im at hz₀
    linarith
  obtain ⟨J,hline,hint⟩ := exists_genuine_physical_lift_integral s w.left realAnchor H
    (height w.theta) w.positive t₀ w.shift hs.le hs1 ha hc.left_neg.le hc.left_fixed
    hμ hμ1 hr hdist hlog hd.positive_support hd.positive_norm hd.shift_small hgap
  refine ⟨J,?_,?_,hint⟩
  · intro x hx
    refine ⟨?_,(hline x hx.1 hx.2).1⟩
    change centerPoint A B e Γ s w+((J:ℂ)+(x:ℂ))∈upperSource H
    simpa only [upperSource,mem_ofPred_eq,Complex.add_im,Complex.natCast_im,
      Complex.ofReal_im,add_zero] using hz₀
  · intro x hx
    exact (hline x hx.1 hx.2).2

def normalizedPhysicalCoefficient (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y P₀ : ℝ) (W : ℝ → Fiber) (J : ℝ → ℕ) (n : ℕ) (s : ℝ) : ℂ :=
  if s=0 then localHorn T n 0 else
    physicalCoefficient A B e Γ Y P₀ s (W s) (J s) n/(scale W s:ℂ)^n

theorem normalized_coefficient_eq_of_period_line (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y P₀ : ℝ) (W : ℝ → Fiber) (J : ℝ → ℕ) (s : ℝ)
    (hs : s≠0) (hline : PeriodLineData A B e Γ Y P₀ s (W s) (J s)) (n : ℕ) :
    normalizedPhysicalCoefficient A B e Γ T Y P₀ W J n s =
      scaledIntegral A B e Γ T Y P₀ W n s := by
  simp only [normalizedPhysicalCoefficient,scaledIntegral,hs,ite_false]
  rw [hline.coefficient n]

theorem parameterExpansion_of_eventuallyEq (f g : ℝ → ℂ) (p : ℂ → ℂ)
    (a : ℕ → ℂ) (m : ℕ) (hzero : f 0=g 0) (he : f=ᶠ[𝓝[>] 0]g)
    (hg : ParameterExpansion g p a m) : ParameterExpansion f p a m := by
  obtain ⟨ha,C,hC,hb⟩ := hg
  refine ⟨ha.trans hzero.symm,C,hC,?_⟩
  filter_upwards [he,hb] with s hs hb
  rwa [hs]

structure PhysicalCoefficientsData (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ) : Prop where
  all_orders : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W
  physical : ∀ᶠ s : ℝ in 𝓝[>] 0, PhysicalFiberData A B e Γ Y P₀ s (W s)
  actual_line : ∀ᶠ s : ℝ in 𝓝[>] 0, PeriodLineData A B e Γ Y P₀ s (W s) (J s)
  exact_scaled_integrals : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ n : ℕ,
    normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s=
      scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n s
  coefficients : ∀ n : ℕ, 1≤n →
      gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V 0)≠0 →
    ∃ a : ℕ → ℂ, a 0=0 ∧ a 1=physicalKappa U H A B e Γ N M Yg V n ∧
      Tendsto (normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n)
        (𝓝[>] 0) (𝓝 (localHorn (actualTransition U H A B e Γ N M Yg V) n 0)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s/
          normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0∈slitPlane) ∧
      ∀ m : ℕ, ParameterExpansion
        (fun s => log (normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s/
          normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n 0)) p a m

theorem physical_coefficients_of_all_orders
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber)
    (hd : AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W) :
    ∃ J : ℝ → ℕ, PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀
      N M M₀ Vold V p r G W J := by
  classical
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0<s := self_mem_nhdsWithin
  have hlt : ∀ᶠ s : ℝ in 𝓝[>] 0, s<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  have hl : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃j : ℕ, PeriodLineData A B e Γ Y P₀ s (W s) j := by
    filter_upwards [hd.actual_fibers,Kneser.ActualSewingTimeAtlas.all_orders_data_time_atlas U H A B K F e Γ
      R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd,hpos,hlt] with s hs ha hsp hsl
    exact exists_period_line_of_fiber_data A B e Γ _ Y η Mg P₀ s (W s) hs hsp hsl ha.1
  let J : ℝ → ℕ := fun s => if h : ∃j : ℕ, PeriodLineData A B e Γ Y P₀ s (W s) j then Classical.choose h else 0
  have hline : ∀ᶠ s : ℝ in 𝓝[>] 0, PeriodLineData A B e Γ Y P₀ s (W s) (J s) := by
    filter_upwards [hl] with s hs
    simpa only [J,hs,↓reduceDIte] using Classical.choose_spec hs
  have heq : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀n : ℕ,
      normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n s=
        scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n s := by
    filter_upwards [hline,hpos] with s hl hs
    exact fun n => normalized_coefficient_eq_of_period_line A B e Γ _ Y P₀ W J s (ne_of_gt hs) hl n
  refine ⟨J,hd,all_orders_data_physical_uniformization U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd,hline,heq,?_⟩
  intro n hn hB
  obtain ⟨a,ha0,ha1,ht,hslit,hall⟩ := hd.coefficients n hn hB
  let f := normalizedPhysicalCoefficient A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W J n
  let g := scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n
  have hfg : f=ᶠ[𝓝[>] 0]g := heq.mono (fun s hs => hs n)
  have hfg0 : f 0=g 0 := by simp only [f,g,normalizedPhysicalCoefficient,scaledIntegral,ite_true]
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

theorem exists_actual_physical_sewn_coefficients :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ, ∃ N M M₀ : ℕ,
    ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ, ∃ W : ℝ → Fiber, ∃ J : ℝ → ℕ,
      PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J := by
  obtain ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,hd⟩ :=
    exists_actual_sewn_all_orders
  obtain ⟨J,hJ⟩ := physical_coefficients_of_all_orders U H A B K F e Γ
    R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W hd
  exact ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,J,hJ⟩

end Kneser.ActualPhysicalSewnCoefficients
end
