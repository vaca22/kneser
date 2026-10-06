import Kneser.RealLensModelStep

/-! Real normalization of the true repelling orbit sum does not require
real prepared polynomial germs. Their values at the common limiting root
give one additive imaginary constant, which cancels in all differences. -/
set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Kneser.RealRepellingCoordinatePhase
open Set Metric Complex Filter
open Kneser.ActualLensModel Kneser.GrowingBandGeometry Kneser.RealLensMidline
open Kneser.ActualReflectedLensMidline Kneser.ActualReflectedLensModel
open Kneser.ActualInverseLensBootstrap Kneser.ActualInverseLensRootLimit
open Kneser.EvenPreparedOrbitDiscs Kneser.ExponentialUnfolding
open scoped Topology BigOperators

def physicalRepelling (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ)
    (e₁ e₂ u : ℂ) : ℂ :=
  lensModel s a b θ e₁ e₂ u-
    ∑' k, descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0

def polynomialImag (e₁ e₂ : ℂ) (r : ℝ) : ℝ := e₁.im*r+e₂.im*r^2

theorem residueSum_im_zero (s a b : ℝ) : (residueSum s a b).im=0 := by
  simp [residueSum]

theorem lensModel_im_real_between (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (har : a<r) (hrb : r<b) :
    (lensModel s a b θ e₁ e₂ r).im=Real.pi/θ+polynomialImag e₁ e₂ r := by
  have hlog : (Complex.log ((b:ℂ)-(r:ℂ))).im=0 := by
    rw [←Complex.ofReal_sub,Complex.log_im]
    exact Complex.arg_ofReal_of_nonneg (sub_nonneg.mpr hrb.le)
  have hpow : (r:ℂ)^2=((r^2:ℝ):ℂ) := by norm_cast
  simp only [lensModel,Complex.add_im,Complex.mul_im,residueSum_im_zero,hlog,hpow,
    Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_mul,add_zero,zero_add,
    bandTime_real_between a b θ r har hrb,polynomialImag]
  ring

theorem real_inverse_model_im_limit (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (hs1 : s<1) (ha : -1<a) (har : a<r) (hrb : r<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hlim : Tendsto (inverseOrbit s (r:ℂ)) atTop (𝓝 (b:ℂ))) :
    Tendsto (fun k => (lensModel s a b θ e₁ e₂ (inverseOrbit s r k)).im)
      atTop (𝓝 (Real.pi/θ+polynomialImag e₁ e₂ b)) := by
  have hreal : ∀ k : ℕ, (inverseOrbit s (r:ℂ) k).im=0 ∧
      a<(inverseOrbit s (r:ℂ) k).re ∧ (inverseOrbit s (r:ℂ) k).re<b := by
    intro k
    simpa only [Kneser.ActualInverseLensDynamics.inverseOrbit_eq_iterate] using
      real_between_inverse_orbit s a b r hs1 ha hfa hfb har hrb k
  have hp : Continuous (polynomialImag e₁ e₂) := by unfold polynomialImag; fun_prop
  have hrLim : Tendsto (fun k => (inverseOrbit s (r:ℂ) k).re) atTop (𝓝 b) := by
    have hc := Complex.continuous_re.continuousAt.tendsto.comp hlim
    change Tendsto (fun k => (inverseOrbit s (r:ℂ) k).re) atTop (𝓝 b) at hc
    exact hc
  have ht := (hp.continuousAt.tendsto.comp hrLim).const_add (Real.pi/θ)
  apply ht.congr'
  apply Eventually.of_forall
  intro k
  dsimp only [Function.comp_def]
  have he : inverseOrbit s (r:ℂ) k=((inverseOrbit s (r:ℂ) k).re:ℂ) := by
    apply Complex.ext <;> simp [(hreal k).1]
  rw [he]
  exact (lensModel_im_real_between s a b θ _ e₁ e₂ (hreal k).2.1 (hreal k).2.2).symm

/-- A genuine inverse step telescopes. Only the actual residual terms and
actual principal inverse orbit appear in this identity. -/
theorem inverse_residual_im_telescope
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ : ℝ) (e₁ e₂ u : ℂ)
    (hstep : ∀ k : ℕ,
      lensModel s a b θ e₁ e₂ (inverseOrbit s u (k+1))-
        lensModel s a b θ e₁ e₂ (inverseOrbit s u k)+1=
        -descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0) :
    ∀ N : ℕ, (∑ k∈Finset.range N,
      (descendedTerm A B Γ 2 (inverseOrbit s u (k+1)) s 0).im)=
      (lensModel s a b θ e₁ e₂ u).im-(lensModel s a b θ e₁ e₂ (inverseOrbit s u N)).im := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    have hh := congrArg Complex.im (hstep N)
    simp only [Complex.add_im,Complex.sub_im,Complex.one_im,add_zero,Complex.neg_im] at hh
    linarith

/-- Real inverse orbits have one common imaginary repelling constant.
No reality assumption on e₁,e₂ is present. Summability and the one-step
identity are the true analytic series assertions, not a phase premise. -/
theorem physicalRepelling_im_real
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r : ℝ) (e₁ e₂ : ℂ)
    (hs1 : s<1) (ha : -1<a) (har : a<r) (hrb : r<b)
    (hfa : unfolding s a=(a:ℂ)) (hfb : unfolding s b=(b:ℂ))
    (hlim : Tendsto (inverseOrbit s (r:ℂ)) atTop (𝓝 (b:ℂ)))
    (hsum : Summable (fun k => ‖descendedTerm A B Γ 2 (inverseOrbit s r (k+1)) s 0‖))
    (hstep : ∀ k : ℕ,
      lensModel s a b θ e₁ e₂ (inverseOrbit s r (k+1))-
        lensModel s a b θ e₁ e₂ (inverseOrbit s r k)+1=
        -descendedTerm A B Γ 2 (inverseOrbit s r (k+1)) s 0) :
    (physicalRepelling A B Γ s a b θ e₁ e₂ r).im=
      Real.pi/θ+polynomialImag e₁ e₂ b := by
  have hseries := (hsum.of_norm.hasSum)
  have ht := (Complex.hasSum_im hseries).tendsto_sum_nat
  have hp := (tendsto_const_nhds (x:=(lensModel s a b θ e₁ e₂ r).im)).sub ht
  have he := inverse_residual_im_telescope A B Γ s a b θ e₁ e₂ r hstep
  have hl : Tendsto (fun k => (lensModel s a b θ e₁ e₂ (inverseOrbit s r k)).im)
      atTop (𝓝 (physicalRepelling A B Γ s a b θ e₁ e₂ r).im) := by
    apply hp.congr'
    apply Eventually.of_forall
    intro k
    simp only [physicalRepelling,Complex.sub_im] at *
    linarith [he k]
  exact tendsto_nhds_unique hl
    (real_inverse_model_im_limit s a b θ r e₁ e₂ hs1 ha har hrb hfa hfb hlim)

theorem physicalRepelling_difference_im_zero
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ r r₀ : ℝ) (e₁ e₂ : ℂ)
    (hr : (physicalRepelling A B Γ s a b θ e₁ e₂ r).im=Real.pi/θ+polynomialImag e₁ e₂ b)
    (hr₀ : (physicalRepelling A B Γ s a b θ e₁ e₂ r₀).im=Real.pi/θ+polynomialImag e₁ e₂ b) :
    (physicalRepelling A B Γ s a b θ e₁ e₂ r-
      physicalRepelling A B Γ s a b θ e₁ e₂ r₀).im=0 := by
  rw [Complex.sub_im,hr,hr₀,sub_self]

end Kneser.RealRepellingCoordinatePhase
end
