import Kneser.ActualGlobalSewingIdentification
import Kneser.FlatSewingLogTransfer

/-! One actual exponential preparation, one actual growing inverse and
one actual Fourier sewing are selected throughout a positive parameter
germ. The true sewn-coordinate integral, divided by the genuine
multiplier-defined Lambda power, has the same coherent all-order
logarithm expansion and the same explicit orbit-series first coefficient.
This theorem concerns the actual Fourier sewing constructed here; it
makes no identification with a separately defined classical Kneser map. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Kneser.ActualSewnAllOrders
open Set Metric Filter Complex
open Kneser.ReflectedOrbitChainCoefficient Kneser.CommonQuadraticBaseline
open Kneser.ActualAllOrderUpperHornBaseline Kneser.ActualGlobalSewingIdentification
open Kneser.ActualHolomorphicGrowingLens Kneser.GrowingBandGeometry
open Kneser.GrowingLensSpatialHolomorphy Kneser.ActualGrowingCoordinateInverse
open Kneser.ActualNormalizedGrowingTransition Kneser.NormalizedGrowingFourier
open Kneser.ActualNormalizedSewing Kneser.FourierSewing Kneser.WeightedFourier
open Kneser.ActualOrderedLambdaFlatness Kneser.FlatSewingLogTransfer
open Kneser.ActualAllOrderHornParameter Kneser.ActualRealNormalizedFirstCoefficient
open Kneser.AllOrderParameterExpansion Kneser.GateFourierDerivative
open Kneser.RealNormalizationAnchor
open scoped Topology

structure Fiber where
  left : ℝ
  right : ℝ
  theta : ℝ
  inverse : ℂ → ℂ
  negative : Space
  positive : Space
  shift : ℂ

def defaultFiber : Fiber := ⟨0,0,1,fun _ => 0,0,0,0⟩

def globalTransition (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (s : ℝ) (w : Fiber) : ℂ → ℂ :=
  transition A B (Γ 1) s w.left w.right w.theta realAnchor ((w.left+w.right)/2)
    (first (e 1) s) (second (e 1) s) w.inverse

def scale (W : ℝ → Fiber) (s : ℝ) : ℝ := lambda (height (W s).theta)

def actualSewnCoordinate (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ : ℝ) (s : ℝ) (w : Fiber) : ℂ → ℂ :=
  sewnCoordinate (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) (height w.theta)
    w.positive (gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)) w.shift

def localHorn (T : ℝ → ℂ → ℂ) (n : ℤ) (s : ℝ) : ℂ :=
  Kneser.realHornCoefficient n (fun t => gateFourierCoefficient n 0 (T t))
    (fun t => gateFourierCoefficient 0 0 (T t)) s

/-- At zero the true parabolic horn coefficient is used. Away from zero
this is the actual interval-integral coefficient of the selected sewing,
scaled by the true sewing Lambda. -/
def scaledIntegral (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y P₀ : ℝ) (W : ℝ → Fiber) (n : ℕ) (s : ℝ) : ℂ :=
  if s=0 then localHorn T n 0 else
    gateFourierCoefficient n 0 (actualSewnCoordinate A B e Γ Y P₀ s (W s))/(scale W s:ℂ)^n

structure FiberData (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y η Mg P₀ s : ℝ) (w : Fiber) : Prop where
  control : LensControl (first (e 1)) (second (e 1)) A B (Γ 1) s w.left w.right w.theta Y η Mg P₀
  inverse_analytic : AnalyticOnNhd ℂ w.inverse (strip w.theta (3*Y+boundaryMargin P₀))
  inverse_identity : ∀ z∈strip w.theta (3*Y+boundaryMargin P₀),
    w.inverse z∈strip w.theta (3*Y) ∧
      repellingCoordinate A B (Γ 1) s w.left w.right w.theta (first (e 1) s) (second (e 1) s) (w.inverse z)=z
  negative_support : w.negative∈Negative
  negative_norm : ‖w.negative‖≤1
  positive_support : ∀ n : ℤ, n<0 → w.positive n=0
  positive_norm : ‖w.positive‖≤1
  shift_bound : ‖w.shift‖≤normalizationConstant (boundaryLoss Y P₀) 64 1 4*lambda (height w.theta)
  shift_small : ‖w.shift‖≤1
  normalized : actualSewnCoordinate A B e Γ Y P₀ s w 0=0
  sewing_identity : ∀ z : ℂ, |z.im|≤sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1 →
    globalTransition A B e Γ s w (z+evaluate (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) w.negative z)=
      z+gateFourierCoefficient 0 0 (globalTransition A B e Γ s w)+
        evaluate (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) w.positive z
  comparison : ∀ n : ℕ, 1≤n →
    ‖gateFourierCoefficient n 0 (actualSewnCoordinate A B e Γ Y P₀ s w)/(lambda (height w.theta):ℂ)^n-
      localHorn T n s‖≤comparisonConstant (boundaryLoss Y P₀) 64 1 4 n*lambda (height w.theta)
  actual_scale : lambda (height w.theta)=Kneser.ActualLambdaFlatness.lambdaFactor s w.left

def physicalKappa (U H A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (N M : ℕ) (Y : ℝ) (V : ℝ → ℂ → ℂ) (n : ℤ) : ℂ :=
  Kneser.hornKappa n
    (gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Y V 0))
    (gateCorrectionCoefficient n 0 (physicalCorrection U H A B e Γ N M Y V))
    (gateCorrectionCoefficient 0 0 (physicalCorrection U H A B e Γ N M Y V))

structure AllOrdersData (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) : Prop where
  baseline : BaselineData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch N M M₀ Yg Vold V p r G
  actual_fibers : ∀ᶠ s : ℝ in 𝓝[>] 0,
    FiberData A B e Γ (actualTransition U H A B e Γ N M Yg V) Y η Mg P₀ s (W s)
  flat : ∀ m : ℕ, ∀ᶠ s : ℝ in 𝓝[>] 0, 0<scale W s ∧ scale W s≤s^m
  coefficients : ∀ n : ℕ, 1≤n → gateFourierCoefficient n 0 (actualTransition U H A B e Γ N M Yg V 0)≠0 →
    ∃ a : ℕ → ℂ, a 0=0 ∧ a 1=physicalKappa U H A B e Γ N M Yg V n ∧
      Tendsto (scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n) (𝓝[>] 0)
        (𝓝 (localHorn (actualTransition U H A B e Γ N M Yg V) n 0)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n s /
        scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n 0∈slitPlane) ∧
      ∀ m : ℕ, ParameterExpansion
        (fun s => log (scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n s /
          scaledIntegral A B e Γ (actualTransition U H A B e Γ N M Yg V) Y P₀ W n 0)) p a m

/-- The actual sewing certificate is retained by one selected family.
Selection outside the proved parameter germ uses the explicit default
fiber and has no effect on the eventual statements. -/
theorem all_orders_of_sewn_family
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (hf : SewnFamily U H A B K F e Γ) :
    ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ, ∃ N M M₀ : ℕ,
    ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ, ∃ W : ℝ → Fiber,
      AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W := by
  classical
  obtain ⟨R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,hbase,hglobal⟩ := hf
  let T := actualTransition U H A B e Γ N M Yg V
  have hex : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ w : Fiber, FiberData A B e Γ T Y η Mg P₀ s w := by
    filter_upwards [hglobal] with s hs
    obtain ⟨a,b,θ,Vg,hc,hVan,hVs,hw,hgauge,hscale⟩ := hs
    obtain ⟨Q,P,ζ,hneg,hQ,hpos,hP,hζ,hζ1,hzero,hseam,hcomp⟩ :=
      actual_sewn_coefficient_comparison (height θ) (boundaryLoss Y P₀) _ hw
    refine ⟨⟨a,b,θ,Vg,Q,P,ζ⟩,hc,hVan,hVs,hneg,hQ,hpos,hP,hζ,hζ1,hzero,hseam,?_,hscale⟩
    intro n hn
    have hn0 : (n:ℤ)≠0 := by exact_mod_cast (Nat.ne_zero_of_lt (by omega : 0<n))
    have he := hgauge n hn0
    change localHorn T n s = _ at he
    rw [he]
    exact hcomp n hn
  let W : ℝ → Fiber := fun s => if hs : ∃ w : Fiber, FiberData A B e Γ T Y η Mg P₀ s w
    then Classical.choose hs else defaultFiber
  have hW : ∀ᶠ s : ℝ in 𝓝[>] 0, FiberData A B e Γ T Y η Mg P₀ s (W s) := by
    filter_upwards [hex] with s hs
    dsimp only [W]
    rw [dif_pos hs]
    exact Classical.choose_spec hs
  have hflat : ∀ m : ℕ, ∀ᶠ s : ℝ in 𝓝[>] 0, 0<scale W s ∧ scale W s≤s^m := by
    intro m
    filter_upwards [hW,actual_control_lambda_flat (first (e 1)) (second (e 1)) A B (Γ 1) m] with s hs hfl
    exact hfl _ _ _ _ _ _ _ hs.control
  refine ⟨R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,hbase,hW,hflat,?_⟩
  intro n hn hB
  obtain ⟨a,ha0,hlog,ha1⟩ := hbase.physical_first n hB
  obtain ⟨_a,_ha0,_halog,hbranch,_hid⟩ := hbase.coherent n hB
  let g := localHorn T n
  let f := scaledIntegral A B e Γ T Y P₀ W n
  have hg0 : g 0≠0 := mul_ne_zero hB (Complex.exp_ne_zero _)
  have hf0 : f 0=g 0 := by simp [f,scaledIntegral,g]
  have hlogs : ∀ m : ℕ, ParameterExpansion (fun s => log (g s/g 0)) p a m := hlog
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, g s/g 0∈slitPlane := hbranch
  let D := comparisonConstant (boundaryLoss Y P₀) 64 1 4 n
  have hD : 0≤D := by
    unfold D comparisonConstant hornSizeConstant normalizationConstant hornErrorConstant gapFactor pointFactor
    positivity
  have herr : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s-g s‖≤D*scale W s := by
    filter_upwards [hW,self_mem_nhdsWithin] with s hs hsp
    change 0<s at hsp
    simpa only [f,g,scaledIntegral,if_neg (ne_of_gt hsp),scale,D] using hs.comparison n hn
  obtain ⟨hlim,hslit,hall⟩ := all_orders_log_of_flat_comparison f g (scale W) p a hg0 hf0
    hbase.parameter_analytic hbase.parameter_zero hbase.parameter_derivative hlogs hb D hD herr
    (fun m => (hflat m).mono fun _ hs => hs.2)
  refine ⟨a,ha0,ha1,hlim,?_,?_⟩
  · change ∀ᶠ s : ℝ in 𝓝[>] 0, f s/f 0∈slitPlane
    rw [hf0]
    exact hslit
  · intro m
    change ParameterExpansion (fun s => log (f s/f 0)) p a m
    rw [hf0]
    exact hall m

/-- Unconditional all-mode, all-order endpoint for the true Fourier sewing
of the actual exponential unfolding, with its actual Lambda and explicit
orbit-series first correction. -/
theorem exists_actual_sewn_all_orders :
    ∃ U H A B : ℂ → ℂ, ∃ K : ℂ → ℂ → ℂ, ∃ F : ℂ × ℂ → ℂ,
    ∃ e : (n : ℕ) → Fin (2*n) → ℂ → ℂ, ∃ Γ : ℕ → ℂ × ℂ → ℂ,
    ∃ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ, ∃ N M M₀ : ℕ,
    ∃ Vold V : ℝ → ℂ → ℂ, ∃ p r G : ℂ → ℂ, ∃ W : ℝ → Fiber,
      AllOrdersData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W := by
  obtain ⟨U,H,A,B,K,F,e,Γ,hf⟩ := exists_actual_global_sewn_horn_family
  obtain ⟨R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,ha⟩ :=
    all_orders_of_sewn_family U H A B K F e Γ hf
  exact ⟨U,H,A,B,K,F,e,Γ,R,Rₛ,Y₁,Y₀,Mh,Ch,Yg,Y,η,Mg,P₀,N,M,M₀,Vold,V,p,r,G,W,ha⟩

end Kneser.ActualSewnAllOrders
end
