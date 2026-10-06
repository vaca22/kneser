import Kneser.ActualPhysicalSewnCoefficients
import Kneser.ActualEntireRepellingCoordinate

/-! The same actual physical sewing is glued to its genuine entire
repelling Poincare chart on the whole lower source. The upper Koenigs
inverse keeps its actual cuts. All previously proved coefficients refer
to the unchanged upper function on their genuine period line. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Kneser.ActualGluedPhysicalSewing
open Set Metric Filter Complex
open Kneser.ActualSewnAllOrders Kneser.ActualFiberKoenigsUniformization
open Kneser.ActualPhysicalSewnCoefficients Kneser.ActualFiberRegularWelding
open Kneser.ActualEntireRepellingCoordinate Kneser.ActualSewingTimeAtlas
open Kneser.ActualRegularWelding Kneser.NormalizedGrowingFourier
open Kneser.CommonQuadraticBaseline Kneser.ActualAllOrderUpperHornBaseline
open Kneser.GrowingBandGeometry Kneser.GrowingStripFourier
open Kneser.FourierSewing Kneser.ExponentialUnfolding Kneser.RealNormalizationAnchor
open scoped Topology Classical

def lowerTimeSource (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : Set ℂ :=
  {z | centerPoint A B e Γ s w+z∈lowerSource (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1)}

def lowerTime (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (z : ℂ) : ℂ :=
  lowerMap (sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1) w.negative
    (centerPoint A B e Γ s w+z)

def gluedDomain (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : Set ℂ :=
  physicalDomain A B e Γ Y P₀ s w ∪ lowerTimeSource A B e Γ Y P₀ s w

def gluedFunction (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z∈physicalDomain A B e Γ Y P₀ s w then physicalFunction A B e Γ Y P₀ s w z
  else S (lowerTime A B e Γ Y P₀ s w z)

theorem lower_source_isOpen (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) : IsOpen (lowerTimeSource A B e Γ Y P₀ s w) :=
  (lowerSource_isOpen _).preimage (continuous_const.add continuous_id)

theorem glued_upper_eq (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ) (z : ℂ)
    (hz : z∈physicalDomain A B e Γ Y P₀ s w) :
    gluedFunction A B e Γ Y P₀ s w S z=physicalFunction A B e Γ Y P₀ s w z := by
  simp only [gluedFunction,hz,ite_true]

structure GluedPhysicalData (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (Y P₀ s : ℝ) (w : Fiber) (S : ℂ → ℂ) : Prop where
  physical : PhysicalFiberData A B e Γ Y P₀ s w
  repelling_analytic : ∀z, AnalyticAt ℂ S z
  repelling_normalized : S 0=(((w.left+w.right)/2:ℝ):ℂ)
  repelling_abel : ∀z, S (z+1)=unfolding s (S z)
  repelling_period : ∀z, S (z+repellingPeriod s w.right)=S z
  upper_subset : physicalDomain A B e Γ Y P₀ s w ⊆ gluedDomain A B e Γ Y P₀ s w
  lower_subset : lowerTimeSource A B e Γ Y P₀ s w ⊆ gluedDomain A B e Γ Y P₀ s w
  domain_open : IsOpen (gluedDomain A B e Γ Y P₀ s w)
  zero_mem : (0:ℂ)∈gluedDomain A B e Γ Y P₀ s w
  analytic : AnalyticOnNhd ℂ (gluedFunction A B e Γ Y P₀ s w S) (gluedDomain A B e Γ Y P₀ s w)
  normalized : gluedFunction A B e Γ Y P₀ s w S 0=(realAnchor:ℂ)
  upper_eq : ∀z∈physicalDomain A B e Γ Y P₀ s w,
    gluedFunction A B e Γ Y P₀ s w S z=physicalFunction A B e Γ Y P₀ s w z
  lower_eq : ∀z∈lowerTimeSource A B e Γ Y P₀ s w,
    gluedFunction A B e Γ Y P₀ s w S z=S (lowerTime A B e Γ Y P₀ s w z)
  abel : ∀z∈gluedDomain A B e Γ Y P₀ s w,
    z+1∈gluedDomain A B e Γ Y P₀ s w ∧
      gluedFunction A B e Γ Y P₀ s w S (z+1)=unfolding s (gluedFunction A B e Γ Y P₀ s w S z)

theorem exists_glued_of_fiber_data (A B : ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (T : ℝ → ℂ → ℂ) (Y η Mg P₀ s : ℝ) (w : Fiber)
    (hs : 0<s) (hs1 : s<1/2) (hd : FiberData A B e Γ T Y η Mg P₀ s w)
    (hp : PhysicalFiberData A B e Γ Y P₀ s w) :
    ∃ S : ℂ → ℂ, GluedPhysicalData A B e Γ Y P₀ s w S := by
  have hc := hd.control
  have har : w.left<(w.left+w.right)/2 := by linarith [hc.left_neg,hc.right_pos]
  have hrb : (w.left+w.right)/2<w.right := by linarith [hc.left_neg,hc.right_pos]
  obtain ⟨S,hSa,hS0,hSabel,hSperiod,hSmatch⟩ := exists_actual_entire_repelling_of_control
    (first (e 1)) (second (e 1)) A B (Γ 1) s w.left w.right w.theta Y η Mg P₀
      ((w.left+w.right)/2) hs hs1 hc har hrb
  have hSlens := hSmatch w.inverse hd.inverse_identity
  let H := sewingWidth (height w.theta) (boundaryLoss Y P₀) 64 1
  let c := centerPoint A B e Γ s w
  have hoverlap : ∀z∈physicalDomain A B e Γ Y P₀ s w,
      z∈lowerTimeSource A B e Γ Y P₀ s w →
      physicalFunction A B e Γ Y P₀ s w z=S (lowerTime A B e Γ Y P₀ s w z) := by
    intro z hz hzl
    have hu : 1-H<(c+z).im := hz.1
    have hl : (c+z).im<H-1 := hzl
    have hband : c+z∈symmetricStrip (H-1) := by
      change |(c+z).im|<H-1
      exact abs_lt.mpr ⟨by linarith,hl⟩
    have he := hp.seam (c+z) hband
    rw [show c+z-c=z by ring] at he
    have hm := lowerMap_mem_regular_strip (height w.theta) (boundaryLoss Y P₀)
      (outerWidth w.theta Y P₀) w.negative hd.negative_norm (c+z)
      (show c+z∈symmetricStrip H from by change |(c+z).im|<H; change |(c+z).im|<H-1 at hband; linarith) rfl
    have hS := hSlens _ hm
    change physicalFunction A B e Γ Y P₀ s w z=
      regularRepellingInverse A B (Γ 1) s w.left w.right w.theta ((w.left+w.right)/2)
        (first (e 1) s) (second (e 1) s) w.inverse (lowerMap H w.negative (c+z)) at he
    exact he.trans hS.symm
  have hlower : ∀z∈lowerTimeSource A B e Γ Y P₀ s w,
      gluedFunction A B e Γ Y P₀ s w S z=S (lowerTime A B e Γ Y P₀ s w z) := by
    intro z hz
    by_cases hu : z∈physicalDomain A B e Γ Y P₀ s w
    · rw [glued_upper_eq A B e Γ Y P₀ s w S z hu]
      exact hoverlap z hu hz
    · simp only [gluedFunction,hu,ite_false]
  have hupper : ∀z∈physicalDomain A B e Γ Y P₀ s w,
      gluedFunction A B e Γ Y P₀ s w S z=physicalFunction A B e Γ Y P₀ s w z :=
    glued_upper_eq A B e Γ Y P₀ s w S
  have hla : AnalyticOnNhd ℂ (fun z => S (lowerTime A B e Γ Y P₀ s w z))
      (lowerTimeSource A B e Γ Y P₀ s w) := by
    intro z hz
    have ht := (hp.regular.atlas.lower_analytic (c+z) hz).comp
      (f:=fun v : ℂ => c+v) (analyticAt_const.add analyticAt_id)
    exact (hSa _).comp ht
  have hglue : AnalyticOnNhd ℂ (gluedFunction A B e Γ Y P₀ s w S) (gluedDomain A B e Γ Y P₀ s w) := by
    intro z hz
    rcases hz with hu|hl
    · apply (hp.analytic z hu).congr
      filter_upwards [hp.domain_open.mem_nhds hu] with v hv
      exact (hupper v hv).symm
    · apply (hla z hl).congr
      filter_upwards [(lower_source_isOpen A B e Γ Y P₀ s w).mem_nhds hl] with v hv
      exact (hlower v hv).symm
  refine ⟨S,hp,hSa,hS0,hSabel,hSperiod,fun _ hz => Or.inl hz,fun _ hz => Or.inr hz,
    hp.domain_open.union (lower_source_isOpen A B e Γ Y P₀ s w),Or.inl hp.zero_mem,hglue,
    (hupper 0 hp.zero_mem).trans hp.normalized,hupper,hlower,?_⟩
  intro z hz
  rcases hz with hu|hl
  · obtain ⟨hu1,he⟩ := hp.abel z hu
    refine ⟨Or.inl hu1,?_⟩
    rw [hupper (z+1) hu1,hupper z hu,he]
  · have hl1 : z+1∈lowerTimeSource A B e Γ Y P₀ s w := by
      change (c+(z+1)).im<H-1
      change (c+z).im<H-1 at hl
      simpa only [add_assoc,Complex.add_im,Complex.one_im,add_zero] using hl
    refine ⟨Or.inr hl1,?_⟩
    rw [hlower (z+1) hl1,hlower z hl]
    have ht : lowerTime A B e Γ Y P₀ s w (z+1)=lowerTime A B e Γ Y P₀ s w z+1 := by
      unfold lowerTime
      rw [←add_assoc,hp.regular.atlas.lower_translation]
    rw [ht,hSabel]

theorem glued_family_of_physical_coefficients
    (U H A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (F : ℂ × ℂ → ℂ)
    (e : (n : ℕ) → Fin (2*n) → ℂ → ℂ) (Γ : ℕ → ℂ × ℂ → ℂ)
    (R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ : ℝ) (N M M₀ : ℕ)
    (Vold V : ℝ → ℂ → ℂ) (p r G : ℂ → ℂ) (W : ℝ → Fiber) (J : ℝ → ℕ)
    (hd : PhysicalCoefficientsData U H A B K F e Γ R Rₛ Y₁ Y₀ Mh Ch Yg Y η Mg P₀ N M M₀ Vold V p r G W J) :
    ∃ S : ℝ → ℂ → ℂ, ∀ᶠs : ℝ in 𝓝[>] 0,
      GluedPhysicalData A B e Γ Y P₀ s (W s) (S s) := by
  classical
  have hpos : ∀ᶠs : ℝ in 𝓝[>] 0, 0<s := self_mem_nhdsWithin
  have hsmall : ∀ᶠs : ℝ in 𝓝[>] 0, s<1/2 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2)).filter_mono nhdsWithin_le_nhds
  have he : ∀ᶠs : ℝ in 𝓝[>] 0, ∃S : ℂ → ℂ, GluedPhysicalData A B e Γ Y P₀ s (W s) S := by
    filter_upwards [hd.all_orders.actual_fibers,hd.physical,hpos,hsmall] with s hf hp hs hs1
    exact exists_glued_of_fiber_data A B e Γ _ Y η Mg P₀ s (W s) hs hs1 hf hp
  let S : ℝ → ℂ → ℂ := fun s => if h : ∃S : ℂ → ℂ, GluedPhysicalData A B e Γ Y P₀ s (W s) S
    then Classical.choose h else fun _ => 0
  refine ⟨S,?_⟩
  filter_upwards [he] with s hs
  simpa only [S,hs,↓reduceDIte] using Classical.choose_spec hs

end Kneser.ActualGluedPhysicalSewing
end
