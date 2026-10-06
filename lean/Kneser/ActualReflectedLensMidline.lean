import Kneser.ActualReflectedLensModel
import Kneser.RealLensMidline

/-! The genuine principal inverse preserves the entire real interval
between its actual split fixed points and the exact lens midline height. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Kneser.ActualReflectedLensMidline
open Set Metric Complex
open Kneser.ExponentialUnfolding Kneser.RepellingExponentialOrbit
open Kneser.ActualReflectedLensModel Kneser.RealLensMidline
open Kneser.GrowingBandGeometry Kneser.ActualLensGeometry
open scoped Topology

def inverseReal (s r : ℝ) : ℝ := (Real.log (1+r)+s)/(1-s)

theorem inverseStep_ofReal (s r : ℝ) (hr : -1<r) : inverseStep s (r:ℂ)=(inverseReal s r:ℂ) := by
  rw [inverseStep_formula]
  have he : Complex.log (1+(r:ℂ))=(Real.log (1+r):ℂ) := by
    rw [←Complex.ofReal_one,←Complex.ofReal_add,←Complex.ofReal_log (by linarith : 0≤1+r)]
  rw [he]
  simp only [inverseReal,Complex.ofReal_div,Complex.ofReal_add]

theorem inverseReal_fixed (s r : ℝ) (hs : s<1) (hr : unfolding s r=(r:ℂ)) : inverseReal s r=r := by
  have he : Real.exp (-s+(1-s)*r)=1+r := by
    have hh : realStep s r=r := by exact_mod_cast ((unfolding_ofReal s r).symm.trans hr)
    dsimp [realStep] at hh
    linarith
  unfold inverseReal
  rw [←he,Real.log_exp]
  have hn : 1-s≠0 := by linarith
  field_simp
  ring

theorem inverseReal_between (s a b r : ℝ) (hs : s<1) (ha : -1<a)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ)) (har : a<r) (hrb : r<b) :
    a< inverseReal s r ∧ inverseReal s r<b := by
  have h₁ : inverseReal s a< inverseReal s r := by
    unfold inverseReal
    have hh := Real.log_lt_log (by linarith : 0<1+a) (by linarith : 1+a<1+r)
    exact div_lt_div_of_pos_right (by linarith) (by linarith)
  have h₂ : inverseReal s r< inverseReal s b := by
    unfold inverseReal
    have hh := Real.log_lt_log (by linarith : 0<1+r) (by linarith : 1+r<1+b)
    exact div_lt_div_of_pos_right (by linarith) (by linarith)
  rw [inverseReal_fixed s a hs hfa] at h₁
  rw [inverseReal_fixed s b hs hfb] at h₂
  exact ⟨h₁,h₂⟩

theorem physical_inverse_iterate_reflected (s : ℝ) (u : ℂ) (k : ℕ) :
    (inverseStep s)^[k] u=-inverseOrbit (-u) (s:ℂ) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',inverseOrbit_succ,ih]
    simp only [inverseStep,neg_neg]

theorem real_between_inverse_orbit (s a b r : ℝ) (hs : s<1) (ha : -1<a)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ)) (har : a<r) (hrb : r<b) :
    ∀ k : ℕ, ((inverseStep s)^[k] (r:ℂ)).im=0 ∧
      a<((inverseStep s)^[k] (r:ℂ)).re ∧ ((inverseStep s)^[k] (r:ℂ)).re<b := by
  intro k
  induction k with
  | zero => simpa using And.intro (show (r:ℂ).im=0 by simp) (And.intro har hrb)
  | succ k ih =>
    have he : (inverseStep s)^[k] (r:ℂ)=(((inverseStep s)^[k] (r:ℂ)).re:ℂ) := by
      apply Complex.ext <;> simp [ih.1]
    rw [Function.iterate_succ_apply',he,inverseStep_ofReal s _ (by linarith [ih.2.1])]
    have hi := inverseReal_between s a b ((inverseStep s)^[k] (r:ℂ)).re hs ha hfa hfb ih.2.1 ih.2.2
    simpa using And.intro (show (inverseReal s ((inverseStep s)^[k] (r:ℂ)).re:ℂ).im=0 by simp) hi

/-- Every real lens midline inverse orbit remains strictly between the
actual roots, with exactly the genuine half-height. -/
theorem inverse_real_midline_invariant (s a b θ Y : ℝ) (u : ℂ)
    (hs : s<1) (ha : -1<a) (hab : a<b) (hθ : 0<θ) (hY : 0<Y)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hua : u≠(a:ℂ)) (hub : u≠(b:ℂ)) (hui : u.im=0)
    (hband : bandTime a b θ u∈GrowingBandGeometry.strip θ Y) :
    ∀ k : ℕ, (inverseStep s)^[k] u≠(a:ℂ) ∧ (inverseStep s)^[k] u≠(b:ℂ) ∧
      (bandTime a b θ ((inverseStep s)^[k] u)).im=Real.pi/θ ∧
      bandTime a b θ ((inverseStep s)^[k] u)∈GrowingBandGeometry.strip θ (Y/2) := by
  have hu : u=(u.re:ℂ) := by apply Complex.ext <;> simp [hui]
  have hbetween := real_bandTime_between a b θ u.re hab hθ
    (by intro he; apply hua; rw [hu,he]) (by intro he; apply hub; rw [hu,he])
    (by rw [←hu]; exact hY.trans hband.1)
  have htime : (bandTime a b θ u).im=Real.pi/θ := by rw [hu]; exact bandTime_real_between _ _ _ _ hbetween.1 hbetween.2
  have hlevels := hband
  change Y<(bandTime a b θ u).im ∧ (bandTime a b θ u).im<height θ-Y at hlevels
  rw [htime] at hlevels
  intro k
  rw [hu]
  have hk := real_between_inverse_orbit s a b u.re hs ha hfa hfb hbetween.1 hbetween.2 k
  have he : (inverseStep s)^[k] (u.re:ℂ)=(((inverseStep s)^[k] (u.re:ℂ)).re:ℂ) := by
    apply Complex.ext <;> simp [hk.1]
  have ht : (bandTime a b θ ((inverseStep s)^[k] (u.re:ℂ))).im=Real.pi/θ := by
    rw [he]
    exact bandTime_real_between _ _ _ _ hk.2.1 hk.2.2
  refine ⟨?_,?_,ht,?_⟩
  · intro he
    have hh := congrArg Complex.re he
    simp only [Complex.ofReal_re] at hh
    linarith [hk.2.1]
  · intro he
    have hh := congrArg Complex.re he
    simp only [Complex.ofReal_re] at hh
    linarith [hk.2.2]
  · constructor <;> rw [ht] <;> linarith [hlevels.1,hlevels.2]

end Kneser.ActualReflectedLensMidline
end
