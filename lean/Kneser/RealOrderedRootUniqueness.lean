import Kneser.RealExponentialRoots
import Kneser.ActualPreparedRootMatching
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! The real exponential unfolding has globally unique ordered negative
and positive fixed points for 0<s<1. All such true roots, irrespective of
their construction, lie in any prescribed neighborhood for sufficiently
small positive parameters. Consequently every ordered pair matches the
same preparation roots, with no smallness hypothesis on that pair. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Kneser.RealOrderedRootUniqueness

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.RealExponentialRoots
open scoped Topology

theorem realDefect_zero_of_actual_root (s u : ℝ)
    (h : unfolding (s : ℂ) (u : ℂ) = (u : ℂ)) : realDefect s u = 0 := by
  have he : unfolding (s : ℂ) (u : ℂ) = ((realDefect s u + u : ℝ) : ℂ) := by
    simp [unfolding, realDefect, Complex.ofReal_exp]
  rw [he] at h
  have hr := Complex.ofReal_injective h
  linarith

theorem strictConvexOn_realDefect (s : ℝ) (hs : s < 1) :
    StrictConvexOn ℝ univ (realDefect s) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy hxy a b ha hb hab
  have hne : -s + (1 - s) * x ≠ -s + (1 - s) * y := by
    intro he
    have hm : (1 - s) * x = (1 - s) * y := by linarith
    exact hxy (mul_left_cancel₀ (by linarith : 1 - s ≠ 0) hm)
  have h := strictConvexOn_exp.2 (mem_univ _) (mem_univ _) hne ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have he : a * (-s + (1 - s) * x) + b * (-s + (1 - s) * y) =
      -s + (1 - s) * (a * x + b * y) := by
    calc
      _ = (a + b) * (-s) + (1 - s) * (a * x + b * y) := by ring
      _ = _ := by rw [hab]; ring
  rw [he] at h
  dsimp only [realDefect]
  nlinarith

theorem no_three_actual_real_roots (s x y z : ℝ) (hs : s < 1)
    (hxy : x < y) (hyz : y < z)
    (hx : unfolding (s : ℂ) (x : ℂ) = (x : ℂ))
    (hy : unfolding (s : ℂ) (y : ℂ) = (y : ℂ))
    (hz : unfolding (s : ℂ) (z : ℂ) = (z : ℂ)) : False := by
  have hseg : y ∈ openSegment ℝ x z := by
    rw [openSegment_eq_Ioo (hxy.trans hyz)]
    exact ⟨hxy, hyz⟩
  have h := (strictConvexOn_realDefect s hs).lt_on_openSegment
    (mem_univ x) (mem_univ z) (ne_of_lt (hxy.trans hyz)) hseg
  rw [realDefect_zero_of_actual_root s x hx, realDefect_zero_of_actual_root s y hy,
    realDefect_zero_of_actual_root s z hz, max_self] at h
  exact lt_irrefl 0 h

theorem ordered_actual_roots_unique (s a b a' b' : ℝ) (hs : s < 1)
    (ha : a < 0) (hb : 0 < b) (ha' : a' < 0) (hb' : 0 < b')
    (hfa : unfolding (s : ℂ) (a : ℂ) = (a : ℂ))
    (hfb : unfolding (s : ℂ) (b : ℂ) = (b : ℂ))
    (hfa' : unfolding (s : ℂ) (a' : ℂ) = (a' : ℂ))
    (hfb' : unfolding (s : ℂ) (b' : ℂ) = (b' : ℂ)) : a = a' ∧ b = b' := by
  constructor
  · apply le_antisymm
    · exact le_of_not_gt (fun h => no_three_actual_real_roots s a' a b hs h (ha.trans hb) hfa' hfa hfb)
    · exact le_of_not_gt (fun h => no_three_actual_real_roots s a a' b hs h (ha'.trans hb) hfa hfa' hfb)
  · apply le_antisymm
    · exact le_of_not_gt (fun h => no_three_actual_real_roots s a b' b hs (ha.trans hb') h hfa hfb' hfb)
    · exact le_of_not_gt (fun h => no_three_actual_real_roots s a b b' hs (ha.trans hb) h hfa hfb hfb')

/-- Every actual ordered pair is small, rather than merely the pair
selected by an intermediate-value existence proof. -/
theorem exists_uniform_ordered_root_smallness (δ : ℝ) (hδ : 0 < δ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 2 ∧ ∀ s a b : ℝ, 0 < s → s < s₀ →
      a < 0 → 0 < b → unfolding (s : ℂ) (a : ℂ) = (a : ℂ) →
      unfolding (s : ℂ) (b : ℂ) = (b : ℂ) → |a| < δ ∧ |b| < δ := by
  obtain ⟨s₀, hs₀, hs₀half, hroots⟩ := exists_ordered_small_real_roots δ hδ
  refine ⟨s₀, hs₀, hs₀half, ?_⟩
  intro s a b hs hss ha hb hfa hfb
  obtain ⟨a', b', ha'δ, ha', hb', hb'δ, hfa', hfb'⟩ := hroots s hs hss
  have hsl : s < 1 := by linarith
  obtain ⟨rfl, rfl⟩ := ordered_actual_roots_unique s a b a' b' hsl ha hb ha' hb' hfa hfb hfa' hfb'
  exact ⟨by rw [abs_of_neg ha']; linarith, by rw [abs_of_pos hb']; exact hb'δ⟩

theorem eventually_all_ordered_roots_small (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ a b : ℝ, a < 0 → 0 < b →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) →
      unfolding (s : ℂ) (b : ℂ) = (b : ℂ) → |a| < δ ∧ |b| < δ := by
  obtain ⟨s₀, hs₀, _hs₀half, hsmall⟩ := exists_uniform_ordered_root_smallness δ hδ
  have hp : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hl : ∀ᶠ s : ℝ in 𝓝[>] 0, s < s₀ :=
    (eventually_lt_nhds hs₀).filter_mono nhdsWithin_le_nhds
  filter_upwards [hp, hl] with s hs hss
  exact fun a b => hsmall s a b hs hss

/-- Uniform matching of arbitrary actual ordered roots to the SAME
analytic preparation branches. Root smallness is a proved conclusion. -/
theorem exists_uniform_actual_root_matching (U H e₁ e₂ A B : ℂ → ℂ)
    (K : ℂ → ℂ → ℂ) (F Γ : ℂ × ℂ → ℂ)
    (hdata : Kneser.ReflectedOrbitChainCoefficient.ActualPreparationData U H e₁ e₂ A B K F Γ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s a b : ℝ, 0 < s → s < s₀ → a < 0 → 0 < b →
      unfolding (s : ℂ) (a : ℂ) = (a : ℂ) → unfolding (s : ℂ) (b : ℂ) = (b : ℂ) →
      ∀ x : ℂ, x ^ 2 = (s : ℂ) →
        (U x = (a : ℂ) ∧ U (-x) = (b : ℂ)) ∨
          (U x = (b : ℂ) ∧ U (-x) = (a : ℂ)) := by
  obtain ⟨δ, s₁, hδ, hs₁, hmatch⟩ :=
    Kneser.ActualPreparedRootMatching.exists_root_matching_neighborhood U H e₁ e₂ A B K F Γ hdata
  obtain ⟨s₂, hs₂, _hs₂half, hsmall⟩ := exists_uniform_ordered_root_smallness δ hδ
  refine ⟨min s₁ s₂, lt_min hs₁ hs₂, ?_⟩
  intro s a b hs hss ha hb hfa hfb x hx
  obtain ⟨haδ, hbδ⟩ := hsmall s a b hs (hss.trans_le (min_le_right _ _)) ha hb hfa hfb
  exact hmatch s a b hs (hss.trans_le (min_le_left _ _)) haδ hbδ (ha.trans hb) hfa hfb x hx

/-- Existence holds throughout the whole saddle-node real interval, not
only on the small parameter interval needed by the preparation. -/
theorem exists_ordered_actual_roots (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧ unfolding (s : ℂ) (a : ℂ) = (a : ℂ) ∧
      unfolding (s : ℂ) (b : ℂ) = (b : ℂ) := by
  let c : ℝ := 1 - s
  have hc : 0 < c := by dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  let w : ℝ := 4 / c
  let u : ℝ := (w + s) / c
  have hwc : c * w = 4 := by dsimp [w]; field_simp
  have huc : c * u = w + s := by dsimp [u]; field_simp
  have hw : 4 ≤ w := by
    dsimp [w]
    apply (le_div_iff₀ hc).mpr
    linarith
  have hu : 0 < u := by dsimp [u]; positivity
  have hww : c * w ^ 2 = 4 * w := by
    calc
      _ = (c * w) * w := by ring
      _ = _ := by rw [hwc]
  have hul : u < w ^ 2 / 2 := by
    apply (mul_lt_mul_iff_right₀ hc).mp
    nlinarith
  have harg : -s + (1 - s) * u = w := by change -s + c * u = w; linarith
  have hplus : 0 < realDefect s u := by
    dsimp only [realDefect]
    rw [harg]
    have hq := Real.quadratic_le_exp_of_nonneg (by linarith : 0 ≤ w)
    linarith
  have hminus : 0 < realDefect s (-1) := by
    have ha : -s + (1 - s) * (-1) = -1 := by ring
    dsimp only [realDefect]
    rw [ha]
    linarith [Real.exp_pos (-1)]
  have hzero : realDefect s 0 < 0 := by
    dsimp [realDefect]
    simp only [mul_zero, add_zero, sub_zero]
    exact sub_neg.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hcont : Continuous (realDefect s) := by unfold realDefect; fun_prop
  obtain ⟨a, hai, haroot⟩ := intermediate_value_Icc' (by norm_num : (-1 : ℝ) ≤ 0)
    hcont.continuousOn (show (0 : ℝ) ∈ Icc (realDefect s 0) (realDefect s (-1)) from ⟨hzero.le, hminus.le⟩)
  obtain ⟨b, hbi, hbroot⟩ := intermediate_value_Icc hu.le
    hcont.continuousOn (show (0 : ℝ) ∈ Icc (realDefect s 0) (realDefect s u) from ⟨hzero.le, hplus.le⟩)
  have ha : a < 0 := by
    rcases lt_or_eq_of_le hai.2 with ha | ha
    · exact ha
    · rw [← ha, haroot] at hzero; linarith
  have hb : 0 < b := by
    rcases lt_or_eq_of_le hbi.1 with hb | hb
    · exact hb
    · rw [hb, hbroot] at hzero; linarith
  exact ⟨a, b, ha, hb, actual_root_of_realDefect_zero s a haroot,
    actual_root_of_realDefect_zero s b hbroot⟩

theorem exists_unique_ordered_actual_roots (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    ∃! p : ℝ × ℝ, p.1 < 0 ∧ 0 < p.2 ∧
      unfolding (s : ℂ) (p.1 : ℂ) = (p.1 : ℂ) ∧
      unfolding (s : ℂ) (p.2 : ℂ) = (p.2 : ℂ) := by
  obtain ⟨a, b, ha, hb, hfa, hfb⟩ := exists_ordered_actual_roots s hs hs1
  refine ⟨(a, b), ⟨ha, hb, hfa, hfb⟩, ?_⟩
  intro p hp
  obtain ⟨haeq, hbeq⟩ := ordered_actual_roots_unique s p.1 p.2 a b hs1
    hp.1 hp.2.1 ha hb hp.2.2.1 hp.2.2.2 hfa hfb
  exact Prod.ext haeq hbeq

end Kneser.RealOrderedRootUniqueness

end
