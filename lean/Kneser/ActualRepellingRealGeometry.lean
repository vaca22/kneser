import Kneser.ActualGrowingKoenigsIdentification
import Kneser.ActualGrowingCoordinateInverse
import Mathlib.Analysis.Calculus.Deriv.Star

/-! The true repelling growing coordinate, normalized at a real interval
point, has Schwarz reflection. Its genuine injective inverse sends real
values to the actual real interval between the two split roots. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
namespace Kneser.ActualRepellingRealGeometry
open Set Metric Filter Complex
open Kneser.GrowingBandGeometry Kneser.ActualLensModel Kneser.GrowingLensSpatialHolomorphy
open Kneser.ActualGrowingRealPhases Kneser.ActualHolomorphicGrowingLens
open Kneser.ActualGrowingKoenigsIdentification Kneser.RealRepellingCoordinatePhase
open Kneser.ActualGrowingCoordinateInverse Kneser.GrowingLensCoordinateRegularity
open scoped Topology ComplexConjugate

def reflection (θ : ℝ) (Z : ℂ) : ℂ := conj Z+(height θ:ℂ)*I

def normalizedRepelling (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r : ℝ)
    (e₁ e₂ : ℂ) (Z : ℂ) : ℂ :=
  repellingCoordinate A B Γ s a b θ e₁ e₂ Z-physicalRepelling A B Γ s a b θ e₁ e₂ r

theorem reflection_im (θ : ℝ) (Z : ℂ) : (reflection θ Z).im=height θ-Z.im := by
  simp only [reflection,Complex.add_im,Complex.conj_im,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
  ring

theorem reflection_mem_strip (θ Y : ℝ) (Z : ℂ) (hZ : Z∈strip θ Y) : reflection θ Z∈strip θ Y := by
  change Y<(reflection θ Z).im ∧ (reflection θ Z).im<height θ-Y
  rw [reflection_im]
  constructor <;> linarith [hZ.1,hZ.2]

theorem reflection_midline (θ x : ℝ) :
    reflection θ ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)=(x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I := by
  apply Complex.ext
  · simp [reflection]
  · simp only [reflection_im,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,
      Complex.I_re,Complex.I_im,mul_one,mul_zero,zero_add,add_zero,height]
    ring

theorem reflected_analytic (f : ℂ → ℂ) (θ Y : ℝ)
    (hf : AnalyticOnNhd ℂ f (strip θ Y)) :
    AnalyticOnNhd ℂ (fun Z => conj (f (reflection θ Z))) (strip θ Y) := by
  apply DifferentiableOn.analyticOnNhd _ (strip_isOpen θ Y)
  intro Z hZ
  have hout : DifferentiableAt ℂ f (conj Z+(height θ:ℂ)*I) :=
    (hf _ (reflection_mem_strip θ Y Z hZ)).differentiableAt
  have hshift : DifferentiableAt ℂ (fun W : ℂ => W+(height θ:ℂ)*I) (conj Z) :=
    (differentiableAt_id (x:=conj Z)).add_const ((height θ:ℂ)*I)
  have hd := hout.comp (conj Z) hshift
  have hh := differentiableAt_conj_conj_iff.mpr hd
  exact hh.differentiableWithinAt

theorem reflection_of_real_midline (f : ℂ → ℂ) (θ Y : ℝ)
    (hθ : 0<θ) (hwidth : θ*Y≤Real.pi/2)
    (hf : AnalyticOnNhd ℂ f (strip θ Y))
    (hreal : ∀ x : ℝ, (f ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)).im=0) :
    ∀ Z∈strip θ Y, f (reflection θ Z)=conj (f Z) := by
  have he := eqOn_strip_of_midline (fun Z => conj (f (reflection θ Z))) f θ Y hθ hwidth
    (reflected_analytic f θ Y hf) hf (fun x => by
      rw [reflection_midline]
      apply Complex.ext
      · exact Complex.conj_re _
      · rw [Complex.conj_im,hreal x]
        ring)
  intro Z hZ
  have hh := congrArg conj (he hZ)
  simpa only [Complex.conj_conj] using hh

theorem normalizedRepelling_midline_real_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r x : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    (normalizedRepelling A B Γ s a b θ r (e₁ s) (e₂ s)
      ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)).im=0 := by
  have hb := bandChart_midline_between a b θ x (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
  let v : ℝ := (a+b*Real.exp (-θ*x))/(1+Real.exp (-θ*x))
  have he : bandChart a b θ ((x:ℂ)+((Real.pi/θ:ℝ):ℂ)*I)=(v:ℂ) := bandChart_midline a b θ x hc.theta_pos
  have hav : a<v := by simpa only [he,Complex.ofReal_re] using hb.1
  have hvb : v<b := by simpa only [he,Complex.ofReal_re] using hb.2
  have hvr := (actual_real_phases_of_control e₁ e₂ A B Γ s a b θ Y η M P v hs1 hc hav hvb).2
  have hrr := (actual_real_phases_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb).2
  change (physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) (bandChart a b θ _) -
    physicalRepelling A B Γ s a b θ (e₁ s) (e₂ s) r).im=0
  rw [he,Complex.sub_im,hvr,hrr,sub_self]

theorem normalizedRepelling_reflection_of_control
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) :
    ∀ Z∈strip θ Y,
      normalizedRepelling A B Γ s a b θ r (e₁ s) (e₂ s) (reflection θ Z)=
        conj (normalizedRepelling A B Γ s a b θ r (e₁ s) (e₂ s) Z) := by
  have ha : AnalyticOnNhd ℂ (normalizedRepelling A B Γ s a b θ r (e₁ s) (e₂ s)) (strip θ Y) :=
    fun Z hZ => ((actual_coordinates_analytic e₁ e₂ A B Γ s a b θ Y η M P hc).2 Z hZ).sub analyticAt_const
  exact reflection_of_real_midline _ θ Y hc.theta_pos hc.width ha
    (fun x => normalizedRepelling_midline_real_of_control e₁ e₂ A B Γ s a b θ Y η M P r x hs1 hc har hrb)

/-- Real values of the genuine normalized coordinate have actual real
preimages. The conclusion is obtained from true injectivity and derived
reflection, not from a real-inverse premise. -/
theorem actual_normalizedRepelling_real_preimage
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P r : ℝ)
    (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P)
    (har : a<r) (hrb : r<b) (Z : ℂ) (hZ : Z∈strip θ (2*Y))
    (hreal : (normalizedRepelling A B Γ s a b θ r (e₁ s) (e₂ s) Z).im=0) :
    Z.im=height θ/2 ∧ (bandChart a b θ Z).im=0 ∧
      a<(bandChart a b θ Z).re ∧ (bandChart a b θ Z).re<b := by
  have hY : 0≤Y := by linarith [hc.height_large]
  have hrZ := reflection_mem_strip θ (2*Y) Z hZ
  have href := normalizedRepelling_reflection_of_control e₁ e₂ A B Γ s a b θ Y η M P r hs1 hc har hrb
    Z (inner_strip_subset θ Y hY hZ)
  have he : normalizedRepelling A B Γ s a b θ r (e₁ s) (e₂ s) (reflection θ Z)=
      normalizedRepelling A B Γ s a b θ r (e₁ s) (e₂ s) Z := by
    rw [href]
    apply Complex.ext <;> simp [hreal]
  have hraw : repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) (reflection θ Z)=
      repellingCoordinate A B Γ s a b θ (e₁ s) (e₂ s) Z := sub_left_injective he
  have hz := (actual_coordinates_injective_buffered e₁ e₂ A B Γ s a b θ Y η M P hc).2 hrZ hZ hraw
  have him : Z.im=height θ/2 := by
    have hh := congrArg Complex.im hz
    rw [reflection_im] at hh
    linarith
  have hrep : Z=(Z.re:ℂ)+((Real.pi/θ:ℝ):ℂ)*I := by
    apply Complex.ext
    · simp
    · simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_re,
        Complex.I_im,mul_one,mul_zero,add_zero,zero_add]
      rw [him]
      unfold height
      ring
  have hb := bandChart_midline_between a b θ Z.re (by linarith [hc.left_neg,hc.right_pos]) hc.theta_pos
  refine ⟨him,?_,?_⟩
  · rw [hrep,bandChart_midline a b θ Z.re hc.theta_pos]
    exact Complex.ofReal_im _
  · rw [hrep]
    exact hb

end Kneser.ActualRepellingRealGeometry
end
