import Kneser.LocalStripFourierDecay

/-! Full-width Fourier decay and reconstruction from proved analytic
periodicity and bounded displacement on a genuine horizontal strip. -/

noncomputable section
set_option maxHeartbeats 800000
namespace Kneser.GrowingStripFourier

open Filter Set Metric Complex MeasureTheory Kneser.GateFourierDerivative
open Kneser.GateFourierHeight Kneser.StripFourierReconstruction
open Kneser.LocalStripFourierDecay
open scoped Topology Interval Classical

def symmetricStrip (D : ℝ) : Set ℂ := {z | |z.im| < D}

def stripExtension (T : ℂ → ℂ) (D : ℝ) (z : ℂ) : ℂ :=
  if z ∈ symmetricStrip D then T z else z

theorem symmetricStrip_isOpen (D : ℝ) : IsOpen (symmetricStrip D) :=
  isOpen_lt Complex.continuous_im.abs continuous_const

theorem extension_eq (T : ℂ → ℂ) (D : ℝ) (z : ℂ) (hz : z ∈ symmetricStrip D) :
    stripExtension T D z = T z := by simp only [stripExtension,hz,ite_true]

theorem extension_periodic (T : ℂ → ℂ) (D : ℝ)
    (hp : ∀ z ∈ symmetricStrip D, T (z+1)=T z+1) :
    ∀ z, stripExtension T D (z+1)=stripExtension T D z+1 := by
  intro z
  have hm : z+1∈symmetricStrip D ↔ z∈symmetricStrip D := by
    simp only [symmetricStrip,mem_ofPred_eq,Complex.add_im,Complex.one_im,add_zero]
  by_cases hz : z∈symmetricStrip D
  · rw [extension_eq T D _ (hm.mpr hz),extension_eq T D _ hz,hp z hz]
  · simp only [stripExtension,hz,hm,ite_false]

theorem extension_analytic (T : ℂ → ℂ) (D : ℝ)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D)) :
    AnalyticOnNhd ℂ (stripExtension T D) (symmetricStrip D) := by
  intro z hz
  apply (ha z hz).congr
  filter_upwards [(symmetricStrip_isOpen D).mem_nhds hz] with w hw
  exact (extension_eq T D w hw).symm

theorem coefficient_height_eq_zero (n : ℤ) (T : ℂ → ℂ) (D Y : ℝ) (hD : 0<D)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z+1)=T z+1) (hY : |Y|<D) :
    gateFourierCoefficient n Y (stripExtension T D)=gateFourierCoefficient n 0 (stripExtension T D) := by
  apply gateFourier_height_independent n _ Y 0 (extension_periodic T D hp)
  intro z hz
  have hy := (Complex.mem_reProdIm.mp hz).2
  have hsub : uIcc Y 0 ⊆ Ioo (-D) D :=
    ordConnected_Ioo.uIcc_subset (abs_lt.mp hY) (by constructor <;> linarith)
  have hm : z∈symmetricStrip D := abs_lt.mpr (hsub hy)
  exact (extension_analytic T D ha z hm).differentiableAt.differentiableWithinAt

/-- Every selected interior width gives exact full-width exponential decay
for the actual integral coefficients. -/
theorem coefficient_decay_on_inner_strip
    (T : ℂ → ℂ) (D d M : ℝ) (hd : 0<d) (hdD : d<D)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z+1)=T z+1)
    (hb : ∀ z∈symmetricStrip D, ‖T z-z‖≤M) (n : ℤ) :
    ‖gateFourierCoefficient n 0 (stripExtension T D)‖≤M*Real.exp (-2*Real.pi*d*|(n:ℝ)|) := by
  let Y : ℝ := if 0≤(n:ℝ) then -d else d
  have hY : |Y|<D := by dsimp [Y]; split_ifs <;> simpa only [abs_neg,abs_of_pos hd] using hdD
  have hh := gate_coefficient_bound n (stripExtension T D) Y M (by
    intro x _
    have hm : gatePoint Y x∈symmetricStrip D := by simpa [symmetricStrip,gatePoint] using hY
    rw [extension_eq T D _ hm]
    exact hb _ hm)
  rw [coefficient_height_eq_zero n T D Y (lt_trans hd hdD) ha hp hY] at hh
  have he : 2*Real.pi*(n:ℝ)*Y = -2*Real.pi*d*|(n:ℝ)| := by
    dsimp [Y]
    split_ifs with hn
    · rw [abs_of_nonneg hn]; ring
    · rw [abs_of_neg (lt_of_not_ge hn)]; ring
  rwa [he] at hh

theorem summable_coefficients_on_inner_strip (T : ℂ → ℂ) (Y M d : ℝ) (hM : 0 ≤ M)
    (hY : |Y| < d)
    (hdecay : ∀ n : ℤ, ‖gateFourierCoefficient n 0 T‖ ≤
      M * Real.exp (-2 * Real.pi * d * |(n : ℝ)|)) :
    Summable (fun n : ℤ => exp (Kneser.fourierFrequency n * (I * (Y : ℂ))) *
      gateFourierCoefficient n 0 T) := by
  let margin : ℝ := d - |Y|
  let q : ℝ := Real.exp (-2 * Real.pi * margin)
  have hd : 0 < margin := by dsimp [margin]; linarith
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hqlt : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  apply Summable.of_norm_bounded ((summable_integer_geometric q hq hqlt).mul_left M)
  intro n
  have he : ‖exp (Kneser.fourierFrequency n * (I * (Y : ℂ)))‖ =
      Real.exp (-2 * Real.pi * (n : ℝ) * Y) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Kneser.fourierFrequency]
  have hab : -(n : ℝ) * Y ≤ |(n : ℝ)| * |Y| := by
    exact (le_abs_self (-(n : ℝ) * Y)).trans_eq (by simp [abs_mul])
  have hcast : (n.natAbs : ℝ) = |(n : ℝ)| := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs n)
    simpa only [Int.cast_natCast, Int.cast_abs] using h
  rw [norm_mul, he]
  calc
    _ ≤ Real.exp (-2 * Real.pi * (n : ℝ) * Y) *
        (M * Real.exp (-2 * Real.pi * d * |(n : ℝ)|)) :=
      mul_le_mul_of_nonneg_left (hdecay n) (Real.exp_pos _).le
    _ = M * Real.exp (-2 * Real.pi * (n : ℝ) * Y - 2 * Real.pi * d * |(n : ℝ)|) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring_nf
    _ ≤ M * Real.exp (-2 * Real.pi * margin * |(n : ℝ)|) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM
      dsimp [margin]
      nlinarith [Real.pi_pos]
    _ = M * q ^ n.natAbs := by
      dsimp [q]
      rw [← Real.exp_nat_mul, hcast]
      congr 2
      ring


theorem fourier_reconstruction_on_inner_strip
    (T : ℂ → ℂ) (D d M : ℝ) (hd : 0<d) (hdD : d<D) (hM : 0≤M)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z+1)=T z+1)
    (hb : ∀ z∈symmetricStrip D, ‖T z-z‖≤M) (z : ℂ) (hz : |z.im|<d) :
    HasSum (fun n : ℤ => gateFourierCoefficient n 0 (stripExtension T D)*
      exp (Kneser.fourierFrequency n*z)) (T z-z) := by
  have hdecay := coefficient_decay_on_inner_strip T D d M hd hdD ha hp hb
  have hcz : Continuous (displacement (stripExtension T D) z.im) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hg : gatePoint z.im x∈symmetricStrip D := by
      simpa [symmetricStrip,gatePoint] using hz.trans hdD
    exact ((extension_analytic T D ha _ hg).continuousAt.comp
      (Complex.continuous_ofReal.continuousAt.add continuousAt_const)).sub
      (Complex.continuous_ofReal.continuousAt.add continuousAt_const)
  have hhe : ∀ n : ℤ, gateFourierCoefficient n z.im (stripExtension T D)=
      gateFourierCoefficient n 0 (stripExtension T D) :=
    fun n => coefficient_height_eq_zero n T D z.im (lt_trans hd hdD) ha hp (hz.trans hdD)
  have hs : Summable (fun n : ℤ => exp (Kneser.fourierFrequency n*(I*(z.im:ℂ)))*
      gateFourierCoefficient n z.im (stripExtension T D)) := by
    simpa only [hhe] using summable_coefficients_on_inner_strip (stripExtension T D) z.im M d hM hz hdecay
  have hh := hasSum_gate_fourier (stripExtension T D) z.im z.re (extension_periodic T D hp) hcz hs
  have he : gatePoint z.im z.re=z := by apply Complex.ext <;> simp [gatePoint]
  simpa only [hhe,he,displacement,extension_eq T D z (hz.trans hdD)] using hh


theorem coefficient_extension_eq (n : ℤ) (T : ℂ → ℂ) (D : ℝ) (hD : 0 < D) :
    gateFourierCoefficient n 0 (stripExtension T D) = gateFourierCoefficient n 0 T := by
  unfold gateFourierCoefficient
  apply intervalIntegral.integral_congr
  intro x _
  have hg : gatePoint 0 x ∈ symmetricStrip D := by simpa [symmetricStrip,gatePoint] using hD
  dsimp only
  rw [extension_eq T D _ hg]

theorem actual_integral_decay_and_reconstruction
    (T : ℂ → ℂ) (D d M : ℝ) (hd : 0 < d) (hdD : d < D) (hM : 0 ≤ M)
    (ha : AnalyticOnNhd ℂ T (symmetricStrip D))
    (hp : ∀ z ∈ symmetricStrip D, T (z+1) = T z+1)
    (hb : ∀ z ∈ symmetricStrip D, ‖T z-z‖ ≤ M) :
    (∀ n : ℤ, ‖gateFourierCoefficient n 0 T‖ ≤ M * Real.exp (-2*Real.pi*d*|(n:ℝ)|)) ∧
    ∀ z : ℂ, |z.im| < d → HasSum (fun n : ℤ => gateFourierCoefficient n 0 T *
      exp (Kneser.fourierFrequency n*z)) (T z-z) := by
  have hD := lt_trans hd hdD
  constructor
  · intro n
    simpa only [coefficient_extension_eq n T D hD] using coefficient_decay_on_inner_strip T D d M hd hdD ha hp hb n
  · intro z hz
    have hh := fourier_reconstruction_on_inner_strip T D d M hd hdD hM ha hp hb z hz
    simpa only [coefficient_extension_eq _ T D hD] using hh

end Kneser.GrowingStripFourier
end
