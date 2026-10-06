import Kneser.ActualRegularKoenigsInverse

/-! A genuine complete right half-plane in the regular attracting time
domain. It is derived from the actual Koenigs image near its fixed point;
no entire attracting inverse or domain coverage hypothesis is used. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Kneser.ActualRegularTimeHalfPlane
open Filter Set Metric Complex
open Kneser.ExponentialUnfolding Kneser.PositiveKoenigsOrbit Kneser.PositiveLocalKoenigs
open Kneser.HolomorphicInjectiveInverse Kneser.ActualRegularKoenigsInverse
open Kneser.ActualHolomorphicGrowingLens Kneser.GrowingBandGeometry
open Kneser.ActualKoenigsEntryRealPhase Kneser.ActualKoenigsGlobalRealPhase Kneser.PositiveKoenigsPetal
open Kneser.WeightedFourier Kneser.FourierSewing
open scoped Topology

theorem norm_koenigsArgument (s a r₀ : ℝ) (w : ℂ) :
    ‖koenigsArgument s a r₀ w‖=‖koenigsValue s a r₀‖*
      Real.exp (Real.log (multiplier s a)*w.re) := by
  simp only [koenigsArgument,norm_mul,Complex.norm_exp,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem exists_regular_right_halfPlane (s a r₀ : ℝ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1) :
    ∃L : ℝ, ∀w : ℂ, L<w.re → w∈regularTimeDomain s a r₀ := by
  have hb := unit_basin_isOpen s a hs hs1 ha ha0 hfa hμ hμ1
  obtain ⟨_hi,hF⟩ := koenigs_unit_basin_data s a hs hs1 ha ha0 hfa hμ hμ1
  have him : IsOpen (koenigsValue s a '' unitBasin s a) := image_isOpen _ _ hb hF
  have hz : (0:ℂ)∈koenigsValue s a '' unitBasin s a :=
    ⟨a,unit_basin_root s a hfa,koenigsValue_at_root s a hfa⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (him.mem_nhds hz)
  let C := ‖koenigsValue s a r₀‖+1
  have hC : 0<C := by dsimp only [C]; positivity
  have hl : Real.log (multiplier s a)<0 := Real.log_neg hμ hμ1
  have harg : 0<δ/C := div_pos hδ hC
  refine ⟨Real.log (δ/C)/Real.log (multiplier s a),?_⟩
  intro w hw
  have hmul : Real.log (multiplier s a)*w.re<Real.log (δ/C) := by
    have hh := mul_lt_mul_of_neg_left hw hl
    rwa [mul_div_cancel₀ _ (ne_of_lt hl)] at hh
  have he : Real.exp (Real.log (multiplier s a)*w.re)<δ/C := by
    simpa only [Real.exp_log harg] using Real.exp_lt_exp.mpr hmul
  have hn : ‖koenigsArgument s a r₀ w‖<δ := by
    rw [norm_koenigsArgument]
    calc
      ‖koenigsValue s a r₀‖*Real.exp (Real.log (multiplier s a)*w.re) ≤
        C*Real.exp (Real.log (multiplier s a)*w.re) :=
          mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (Real.exp_pos _).le
      _ < C*(δ/C) := mul_lt_mul_of_pos_left he hC
      _ = δ := mul_div_cancel₀ δ (ne_of_gt hC)
  exact hball (by simpa only [mem_ball,dist_zero_right] using hn)

theorem exists_actual_regular_right_halfPlane
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    ∃L : ℝ, ∀w : ℂ, L<w.re →
      w∈regularTimeDomain s a Kneser.RealNormalizationAnchor.realAnchor := by
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  exact exists_regular_right_halfPlane s a _ hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1

theorem exists_actual_holomorphic_right_halfPlane
    (e₁ e₂ A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (s a b θ Y η M P : ℝ)
    (hs : 0<s) (hs1 : s<1) (hc : LensControl e₁ e₂ A B Γ s a b θ Y η M P) :
    ∃L : ℝ,
      {w : ℂ | L<w.re}⊆regularTimeDomain s a Kneser.RealNormalizationAnchor.realAnchor ∧
      AnalyticOnNhd ℂ (regularSuperfunction s a Kneser.RealNormalizationAnchor.realAnchor) {w : ℂ | L<w.re} ∧
      ∀w : ℂ, L<w.re →
        regularSuperfunction s a Kneser.RealNormalizationAnchor.realAnchor (w+1)=
          unfolding s (regularSuperfunction s a Kneser.RealNormalizationAnchor.realAnchor w) := by
  obtain ⟨L,hL⟩ := exists_actual_regular_right_halfPlane e₁ e₂ A B Γ s a b θ Y η M P hs hs1 hc
  have ha := real_root_gt_neg_one s a hc.left_fixed
  have hμ : 0<multiplier s a := by unfold multiplier; exact mul_pos (by linarith) (by linarith)
  have hμ1 : multiplier s a<1 := by unfold multiplier; nlinarith [hc.left_neg]
  have hhol := (regular_domain_holomorphic s a Kneser.RealNormalizationAnchor.realAnchor hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1).2.1
  refine ⟨L,hL,(fun w hw => hhol w (hL w hw)),?_⟩
  intro w hw
  exact (regular_superfunction_abel s a _ hs.le hs1 ha hc.left_neg.le hc.left_fixed hμ hμ1 w (hL w hw)).2

theorem sewn_coordinate_regular_domain (s a r₀ L H h : ℝ) (P : Space) (t₀ ζ z : ℂ)
    (hL : ∀w : ℂ, L<w.re → w∈regularTimeDomain s a r₀)
    (hP : ∀n : ℤ, n<0 → P n=0) (hPn : ‖P‖≤1) (hζ : ‖ζ‖≤1)
    (hgap : 0≤H+(normalizingCentre h t₀+ζ+z).im) (hz : L+2<z.re) :
    sewnCoordinate H h P t₀ ζ z∈regularTimeDomain s a r₀ := by
  have hn : ‖ζ+evaluate H P (normalizingCentre h t₀+ζ+z)‖≤2 :=
    (norm_add_le _ _).trans (by linarith [(norm_evaluate_positive_le H P hP _ hgap).trans hPn])
  have hre := (Complex.abs_re_le_norm (ζ+evaluate H P (normalizingCentre h t₀+ζ+z))).trans hn
  have he := sewnDisplacement_eq H h P t₀ ζ z
  have hh : sewnCoordinate H h P t₀ ζ z=z+(ζ+evaluate H P (normalizingCentre h t₀+ζ+z)) := by
    unfold sewnDisplacement at he
    linear_combination he
  apply hL
  rw [hh,Complex.add_re]
  linarith [le_abs_self (ζ+evaluate H P (normalizingCentre h t₀+ζ+z)).re,
    neg_le_abs (ζ+evaluate H P (normalizingCentre h t₀+ζ+z)).re]

theorem exists_genuine_physical_period_line (s a r₀ H h : ℝ) (P : Space) (t₀ ζ : ℂ)
    (hs : 0≤s) (hs1 : s<1) (ha : -1<a) (ha0 : a≤0)
    (hfa : unfolding s a=(a:ℂ)) (hμ : 0<multiplier s a) (hμ1 : multiplier s a<1)
    (hP : ∀n : ℤ, n<0 → P n=0) (hPn : ‖P‖≤1) (hζ : ‖ζ‖≤1)
    (hgap : 0≤H+(normalizingCentre h t₀+ζ).im) :
    ∃N : ℕ, ∀x : ℝ, 0≤x → x≤1 →
      sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))∈regularTimeDomain s a r₀ ∧
      koenigsValue s a (regularSuperfunction s a r₀ (sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))))=
        koenigsArgument s a r₀ (sewnCoordinate H h P t₀ ζ ((N:ℂ)+(x:ℂ))) := by
  obtain ⟨L,hL⟩ := exists_regular_right_halfPlane s a r₀ hs hs1 ha ha0 hfa hμ hμ1
  obtain ⟨N,hN⟩ := exists_nat_gt (L+2)
  refine ⟨N,?_⟩
  intro x hx _hx1
  have hm := sewn_coordinate_regular_domain s a r₀ L H h P t₀ ζ ((N:ℂ)+(x:ℂ)) hL hP hPn hζ
    (by simpa using hgap) (by simp only [Complex.add_re,Complex.natCast_re,Complex.ofReal_re]; linarith)
  exact ⟨hm,((regular_domain_holomorphic s a r₀ hs hs1 ha ha0 hfa hμ hμ1).2.2 _ hm).2⟩

end Kneser.ActualRegularTimeHalfPlane
end
