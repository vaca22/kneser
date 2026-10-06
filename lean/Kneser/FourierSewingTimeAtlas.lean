import Kneser.FourierSewingGluing
import Kneser.HolomorphicInjectiveInverse

/-! The constructed Fourier corrections give a genuine two-chart time
atlas. Both charts are holomorphic and univalent on whole half-planes,
have holomorphic inverses on their actual open images, cover interior
half-planes, and have one actual continuous periodic seam. No physical
Kneser function or external uniformization identity is asserted here. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.FourierSewing

open Set Filter Metric Complex Kneser.WeightedFourier
open Kneser.HolomorphicInjectiveInverse
open scoped Topology Classical

def lowerSource (H : ℝ) : Set ℂ := {z | z.im < H - 1}
def upperSource (H : ℝ) : Set ℂ := {z | 1 - H < z.im}

theorem halfPlaneLipschitz_unit_gap_of_norm_one (H : ℝ) (a : Space)
    (ha : ‖a‖ ≤ 1) : halfPlaneLipschitz H (1 - H) a < 1 := by
  let q := Real.exp (-2 * Real.pi)
  have hq : 0 < q := Real.exp_pos _
  have hlarge : (25 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    have hh := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)
    nlinarith [Real.pi_gt_three]
  have hqsmall : q ≤ 1 / 25 := by
    dsimp [q]
    rw [show -2 * Real.pi = -(2 * Real.pi) by ring, Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hlarge
  have hden : 0 < 1 - q := by linarith
  rw [halfPlaneLipschitz, show H + (1 - H) = 1 by ring, mul_one]
  change 4 * Real.pi * ‖a‖ * q / (1 - q) ^ 2 < 1
  apply (div_lt_one (sq_pos_of_pos hden)).mpr
  have hcoeff : 4 * Real.pi * ‖a‖ ≤ 16 := by
    have hi := mul_le_mul_of_nonneg_left ha (by positivity : 0 ≤ 4 * Real.pi)
    nlinarith [Real.pi_lt_four]
  have hh := mul_le_mul_of_nonneg_right hcoeff hq.le
  nlinarith [sq_nonneg q]

theorem lowerSource_isOpen (H : ℝ) : IsOpen (lowerSource H) :=
  isOpen_lt Complex.continuous_im continuous_const

theorem upperSource_isOpen (H : ℝ) : IsOpen (upperSource H) :=
  isOpen_lt continuous_const Complex.continuous_im

theorem lowerMap_analytic_jacobian (H : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (hQnorm : ‖Q‖ ≤ 1) :
    ∀ z ∈ lowerSource H, AnalyticAt ℂ (lowerMap H Q) z ∧ deriv (lowerMap H Q) z ≠ 0 := by
  have hk := halfPlaneLipschitz_unit_gap_of_norm_one H (reflection Q)
    (by simpa only [norm_reflection] using hQnorm)
  have he : DifferentiableOn ℂ (evaluate H Q) (lowerSource H) :=
    (differentiableOn_evaluate_negative H Q hQ).mono (fun z hz => by dsimp [lowerSource] at *; linarith)
  intro z hz
  have hd := he.differentiableAt ((lowerSource_isOpen H).mem_nhds hz)
  have hn : ‖deriv (evaluate H Q) z‖ ≤ halfPlaneLipschitz H (1 - H) (reflection Q) := by
    apply norm_deriv_le_of_lip' (by unfold halfPlaneLipschitz; positivity)
    filter_upwards [(lowerSource_isOpen H).mem_nhds hz] with w hw
    convert norm_evaluate_negative_sub_le H Q hQ (H - 1) (by linarith)
      w z (by exact hw.le) (by exact hz.le) using 1
    congr 2
    ring
  have hmap : DifferentiableOn ℂ (lowerMap H Q) (lowerSource H) :=
    differentiableOn_id.add he
  refine ⟨hmap.analyticAt ((lowerSource_isOpen H).mem_nhds hz), ?_⟩
  intro hzero
  have hder : deriv (lowerMap H Q) z = 1 + deriv (evaluate H Q) z :=
    (hasDerivAt_id z |>.add hd.hasDerivAt).deriv
  have hdneg : deriv (evaluate H Q) z = -1 := by rw [hzero] at hder; linear_combination -hder
  rw [hdneg, norm_neg, norm_one] at hn
  linarith

theorem upperMap_analytic_jacobian (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (hPnorm : ‖P‖ ≤ 1) (t₀ : ℂ) :
    ∀ z ∈ upperSource H, AnalyticAt ℂ (upperMap H P t₀) z ∧ deriv (upperMap H P t₀) z ≠ 0 := by
  have hk := halfPlaneLipschitz_unit_gap_of_norm_one H P hPnorm
  have he : DifferentiableOn ℂ (evaluate H P) (upperSource H) :=
    (differentiableOn_evaluate_positive H P hP).mono
      (fun z hz => by dsimp [upperSource] at *; linarith)
  intro z hz
  have hd := he.differentiableAt ((upperSource_isOpen H).mem_nhds hz)
  have hn : ‖deriv (evaluate H P) z‖ ≤ halfPlaneLipschitz H (1 - H) P := by
    apply norm_deriv_le_of_lip' (by unfold halfPlaneLipschitz; positivity)
    filter_upwards [(upperSource_isOpen H).mem_nhds hz] with w hw
    exact norm_evaluate_positive_sub_le_on_halfPlane H P hP (1 - H) (by linarith)
      w z hw.le hz.le
  have hmap : DifferentiableOn ℂ (upperMap H P t₀) (upperSource H) :=
    (differentiableOn_id.add_const t₀).add he
  refine ⟨hmap.analyticAt ((upperSource_isOpen H).mem_nhds hz), ?_⟩
  intro hzero
  have hder : deriv (upperMap H P t₀) z = 1 + deriv (evaluate H P) z :=
    ((hasDerivAt_id z).add_const t₀ |>.add hd.hasDerivAt).deriv
  have hdneg : deriv (evaluate H P) z = -1 := by rw [hzero] at hder; linear_combination -hder
  rw [hdneg, norm_neg, norm_one] at hn
  linarith

/-- A concrete atlas certificate refers to actual maps and their actual
image inverses, rather than assuming inverse charts or coverage. -/
structure TimeAtlas (H h : ℝ) (T : ℂ → ℂ) (Q P : Space) (t₀ ζ : ℂ) : Prop where
  lower_analytic : AnalyticOnNhd ℂ (lowerMap H Q) (lowerSource H)
  upper_analytic : AnalyticOnNhd ℂ (upperMap H P t₀) (upperSource H)
  lower_jacobian : ∀ z ∈ lowerSource H, deriv (lowerMap H Q) z ≠ 0
  upper_jacobian : ∀ z ∈ upperSource H, deriv (upperMap H P t₀) z ≠ 0
  lower_injective : InjOn (lowerMap H Q) (lowerSource H)
  upper_injective : InjOn (upperMap H P t₀) (upperSource H)
  lower_image_open : IsOpen (lowerMap H Q '' lowerSource H)
  upper_image_open : IsOpen (upperMap H P t₀ '' upperSource H)
  lower_inverse_analytic : AnalyticOnNhd ℂ (imageInverse (lowerMap H Q) (lowerSource H))
    (lowerMap H Q '' lowerSource H)
  upper_inverse_analytic : AnalyticOnNhd ℂ (imageInverse (upperMap H P t₀) (upperSource H))
    (upperMap H P t₀ '' upperSource H)
  lower_inverse : ∀ y ∈ lowerMap H Q '' lowerSource H,
    imageInverse (lowerMap H Q) (lowerSource H) y ∈ lowerSource H ∧
      lowerMap H Q (imageInverse (lowerMap H Q) (lowerSource H) y) = y
  upper_inverse : ∀ y ∈ upperMap H P t₀ '' upperSource H,
    imageInverse (upperMap H P t₀) (upperSource H) y ∈ upperSource H ∧
      upperMap H P t₀ (imageInverse (upperMap H P t₀) (upperSource H) y) = y
  lower_cover : {y : ℂ | y.im < H - 2} ⊆ lowerMap H Q '' lowerSource H
  upper_cover : {y : ℂ | 2 - H < (y - t₀).im} ⊆ upperMap H P t₀ '' upperSource H
  domain_cover : lowerSource H ∪ upperSource H = univ
  lower_translation : ∀ z, lowerMap H Q (z + 1) = lowerMap H Q z + 1
  upper_translation : ∀ z, upperMap H P t₀ (z + 1) = upperMap H P t₀ z + 1
  lower_inverse_translation : ∀ y ∈ lowerMap H Q '' lowerSource H,
    imageInverse (lowerMap H Q) (lowerSource H) (y + 1) =
      imageInverse (lowerMap H Q) (lowerSource H) y + 1
  upper_inverse_translation : ∀ y ∈ upperMap H P t₀ '' upperSource H,
    imageInverse (upperMap H P t₀) (upperSource H) (y + 1) =
      imageInverse (upperMap H P t₀) (upperSource H) y + 1
  seam : ∃ γ : ℝ → ℂ, Continuous γ ∧ Function.Injective γ ∧
    (∀ x, γ x ∈ lowerSource H ∩ upperSource H ∧
      ‖γ x - (x : ℂ)‖ ≤ 1 ∧ lowerMap H Q (γ x) = (x : ℂ) ∧
      T (x : ℂ) = upperMap H P t₀ (γ x)) ∧
    (∀ x, γ (x + 1) = γ x + 1) ∧
    range γ = {z : ℂ | z ∈ lowerSource H ∧ (lowerMap H Q z).im = 0}
  normalization : upperMap H P t₀ (normalizingCentre h t₀ + ζ) = (h : ℂ) * I
  normalized_zero : sewnCoordinate H h P t₀ ζ 0 = 0

theorem time_atlas_of_fourier_data (H h : ℝ) (hH : 3 < H)
    (T : ℂ → ℂ) (Q P : Space) (t₀ ζ : ℂ)
    (hQ : Q ∈ Negative) (hQnorm : ‖Q‖ ≤ 1)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (hPnorm : ‖P‖ ≤ 1)
    (hsew : ∀ z : ℂ, |z.im| ≤ H → T (lowerMap H Q z) = upperMap H P t₀ z)
    (hroot : (normalizingCentre h t₀ + ζ) + evaluate H P (normalizingCentre h t₀ + ζ) =
      normalizingCentre h t₀) : TimeAtlas H h T Q P t₀ ζ := by
  have hL := lowerMap_analytic_jacobian H Q hQ hQnorm
  have hU := upperMap_analytic_jacobian H P hP hPnorm t₀
  have hKQ : halfPlaneLipschitz H (-(H - 1)) (reflection Q) < 1 := by
    simpa only [neg_sub] using halfPlaneLipschitz_unit_gap_of_norm_one H (reflection Q)
      (by simpa only [norm_reflection] using hQnorm)
  have hKP := halfPlaneLipschitz_unit_gap_of_norm_one H P hPnorm
  have hiL : InjOn (lowerMap H Q) (lowerSource H) := by
    apply (injOn_negative_sewing H Q hQ (H - 1) (by linarith) hKQ).mono
    intro z hz
    change z.im < H - 1 at hz
    exact hz.le
  have hiU : InjOn (upperMap H P t₀) (upperSource H) := by
    apply (injOn_positive_sewing H P hP (1 - H) (by linarith) hKP t₀).mono
    intro z hz
    change 1 - H < z.im at hz
    exact hz.le
  have hsL := lowerSource_isOpen H
  have hsU := upperSource_isOpen H
  refine ⟨(fun z hz => (hL z hz).1), (fun z hz => (hU z hz).1),
    (fun z hz => (hL z hz).2), (fun z hz => (hU z hz).2), hiL, hiU,
    image_isOpen _ _ hsL hL, image_isOpen _ _ hsU hU,
    analyticOnNhd_imageInverse _ _ hsL hiL hL,
    analyticOnNhd_imageInverse _ _ hsU hiU hU,
    imageInverse_spec _ _, imageInverse_spec _ _, ?_, ?_, ?_,
    lowerMap_translation H Q, upperMap_translation H P t₀, ?_, ?_, ?_, ?_,
    sewnCoordinate_zero H h P t₀ ζ hroot⟩
  · intro y hy
    change y.im < H - 2 at hy
    obtain ⟨z, hz, _hzim, he⟩ := exists_lower_preimage H Q hQ (H - 1) 1 (by norm_num)
      (by linarith) hQnorm hKQ y (by linarith)
    have hb := (Complex.abs_im_le_norm (z - y)).trans hz
    simp only [Complex.sub_im] at hb
    refine ⟨z, ?_, he⟩
    change z.im < H - 1
    linarith [hy, (abs_le.mp hb).2]
  · intro y hy
    change 2 - H < (y - t₀).im at hy
    obtain ⟨z, hz, _hzim, he⟩ := exists_upper_preimage H P hP (1 - H) 1 (by norm_num)
      (by linarith) hPnorm hKP t₀ y (by linarith)
    simp only [Complex.sub_im] at hy
    have hb := (Complex.abs_im_le_norm (z - (y - t₀))).trans hz
    simp only [Complex.sub_im] at hb
    refine ⟨z, ?_, he⟩
    change 1 - H < z.im
    linarith [hy, (abs_le.mp hb).1]
  · ext z
    simp only [lowerSource, upperSource, mem_union, mem_ofPred_eq, mem_univ, iff_true]
    by_cases hz : z.im < H - 1
    · exact Or.inl hz
    · exact Or.inr (by linarith)
  · intro y hy
    obtain ⟨z, hz, he⟩ := hy
    have hz1 : z + 1 ∈ lowerSource H := by simpa only [lowerSource, mem_ofPred_eq, add_im, one_im, add_zero] using hz
    have hh := imageInverse_left _ _ hiL (z + 1) hz1
    rw [lowerMap_translation, he] at hh
    rw [hh, ← he, imageInverse_left _ _ hiL z hz]
  · intro y hy
    obtain ⟨z, hz, he⟩ := hy
    have hz1 : z + 1 ∈ upperSource H := by simpa only [upperSource, mem_ofPred_eq, add_im, one_im, add_zero] using hz
    have hh := imageInverse_left _ _ hiU (z + 1) hz1
    rw [upperMap_translation, he] at hh
    rw [hh, ← he, imageInverse_left _ _ hiU z hz]
  · obtain ⟨γ, hcont, hinj, hnear, hp, him, hrange⟩ := exists_periodic_seam H Q hQ
      (H - 1) 1 (by norm_num) (by linarith) (by linarith) hQnorm hKQ
    refine ⟨γ, hcont, hinj, ?_, hp, ?_⟩
    · intro x
      have hγL : γ x ∈ lowerSource H := by change (γ x).im < H - 1; linarith [(abs_le.mp (him x)).2]
      have hγU : γ x ∈ upperSource H := by change 1 - H < (γ x).im; linarith [(abs_le.mp (him x)).1]
      refine ⟨⟨hγL, hγU⟩, (hnear x).1, (hnear x).2.2, ?_⟩
      rw [← (hnear x).2.2]
      exact hsew (γ x) ((him x).trans (by linarith))
    · rw [hrange]
      ext z
      constructor
      · intro hz
        have hh : z ∈ range γ := by rw [hrange]; exact hz
        obtain ⟨x, rfl⟩ := hh
        exact ⟨by change (γ x).im < H - 1; linarith [(abs_le.mp (him x)).2], hz.2⟩
      · intro hz
        exact ⟨hz.1.le, hz.2⟩
  · unfold upperMap normalizingCentre at *
    linear_combination hroot

theorem TimeAtlas.lower_bijOn_inner_halfPlane (H h : ℝ) (T : ℂ → ℂ)
    (Q P : Space) (t₀ ζ : ℂ) (ha : TimeAtlas H h T Q P t₀ ζ)
    (a : ℝ) (haH : a ≤ H - 2) :
    BijOn (lowerMap H Q) {z : ℂ | z ∈ lowerSource H ∧ (lowerMap H Q z).im < a}
      {y : ℂ | y.im < a} := by
  refine ⟨(fun z hz => hz.2), ha.lower_injective.mono (fun z hz => hz.1), ?_⟩
  intro y hy
  obtain ⟨z, hz, he⟩ := ha.lower_cover (show y.im < H - 2 from hy.trans_le haH)
  refine ⟨z, ⟨hz, ?_⟩, he⟩
  rw [he]
  exact hy

theorem TimeAtlas.upper_bijOn_inner_halfPlane (H h : ℝ) (T : ℂ → ℂ)
    (Q P : Space) (t₀ ζ : ℂ) (ha : TimeAtlas H h T Q P t₀ ζ)
    (a : ℝ) (haH : 2 - H ≤ a) :
    BijOn (upperMap H P t₀)
      {z : ℂ | z ∈ upperSource H ∧ a < (upperMap H P t₀ z - t₀).im}
      {y : ℂ | a < (y - t₀).im} := by
  refine ⟨(fun z hz => hz.2), ha.upper_injective.mono (fun z hz => hz.1), ?_⟩
  intro y hy
  obtain ⟨z, hz, he⟩ := ha.upper_cover (show 2 - H < (y - t₀).im from haH.trans_lt hy)
  refine ⟨z, ⟨hz, ?_⟩, he⟩
  rw [he]
  exact hy

/-- The positive chart approaches its actual constant term uniformly in
the horizontal direction. -/
theorem upper_end_uniform (H : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (t₀ : ℂ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ v : ℝ in atTop, ∀ z : ℂ, v ≤ z.im →
      ‖upperMap H P t₀ z - z - t₀ - coefficient H P 0‖ < ε := by
  let q : ℝ → ℝ := fun v => Real.exp (-2 * Real.pi * (H + v))
  have hq : Tendsto q atTop (𝓝 0) := by
    have hv : Tendsto (fun v : ℝ => H + v) atTop atTop :=
      tendsto_atTop_add_const_left atTop H tendsto_id
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hv.const_mul_atTop (by positivity : 0 < 2 * Real.pi))
    convert hh using 1
    funext v
    unfold q
    congr 1
    ring
  have hb : Tendsto (fun v => ‖P‖ * q v / (1 - q v)) atTop (𝓝 0) := by
    have hden : Tendsto (fun v : ℝ => 1 - q v) atTop (𝓝 (1 : ℝ)) := by
      simpa only [sub_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub hq)
    have hh := (hq.const_mul ‖P‖).div hden (by norm_num : (1 : ℝ) ≠ 0)
    change Tendsto (fun v : ℝ => ‖P‖ * q v / (1 - q v)) atTop (𝓝 (‖P‖ * 0 / 1)) at hh
    simpa only [mul_zero, zero_div] using hh
  filter_upwards [eventually_ge_atTop (1 - H), hb.eventually (gt_mem_nhds hε)] with v hv hbound
  intro z hz
  have h := norm_evaluate_positive_sub_constant_le H v (by linarith) P hP z hz
  have he : upperMap H P t₀ z - z - t₀ - coefficient H P 0 =
      evaluate H P z - coefficient H P 0 := by unfold upperMap; ring
  rw [he]
  exact h.trans_lt hbound

/-- The negative chart is normalized to the identity at its genuine
lower end, uniformly in the horizontal direction. -/
theorem lower_end_uniform (H : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ v : ℝ in atBot, ∀ z : ℂ, z.im ≤ v → ‖lowerMap H Q z - z‖ < ε := by
  have hp := upper_end_uniform H (reflection Q) (reflection_negative_is_positive Q hQ) 0 ε hε
  have hh : ∀ᶠ v : ℝ in atBot, ∀ z : ℂ, -v ≤ z.im →
      ‖upperMap H (reflection Q) 0 z - z - 0 - coefficient H (reflection Q) 0‖ < ε :=
    tendsto_neg_atBot_atTop.eventually hp
  filter_upwards [hh] with v hv
  intro z hz
  have hi := hv (-z) (by simp only [Complex.neg_im]; linarith)
  have hzero : coefficient H (reflection Q) 0 = 0 := by
    rw [coefficient_reflection]
    simp only [neg_zero, coefficient, hQ 0 (by norm_num), zero_div]
  simpa only [upperMap, add_zero, sub_zero, add_sub_cancel_left, hzero,
    evaluate_reflection, neg_neg, lowerMap, add_sub_cancel_left] using hi

end Kneser.FourierSewing
end
