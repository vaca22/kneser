import Kneser.ParabolicFatouHolomorphic
import Kneser.RepellingFatouCoordinate
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-!
The actual canonical parabolic coordinates have nonvanishing spatial
derivatives and are univalent on sufficiently deep full petals.  The
reciprocal-coordinate tail and its Cauchy estimate are derived internally.
-/

noncomputable section

namespace Kneser.ParabolicCoordinateJacobian

open Filter Set Metric Kneser.ParabolicExponentialOrbit
open scoped Topology BigOperators

def halfPlane (R : ℝ) : Set ℂ := {z | R < z.re}

theorem halfPlane_isOpen (R : ℝ) : IsOpen (halfPlane R) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem halfPlane_convex (R : ℝ) : Convex ℝ (halfPlane R) := by
  exact convex_halfSpace_re_gt R

theorem inverseCoordinate_involutive (u : ℂ) : inverseCoordinate (inverseCoordinate u) = u := by
  by_cases hu : u = 0
  · simp [hu, inverseCoordinate]
  · dsimp [inverseCoordinate]
    field_simp

theorem sum_range_reciprocal_sq_le (r : ℝ) (hr : 1 ≤ r) (n : ℕ) :
    (∑ k ∈ Finset.range n, 1 / (r + (k : ℝ) / 2) ^ 2) ≤
      4 / r - 4 / (r + (n : ℝ) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    let a : ℝ := r + (n : ℝ) / 2
    have ha : 1 ≤ a := by dsimp [a]; linarith
    have hapos : 0 < a := by linarith
    have haypos : 0 < a + 1 / 2 := by linarith
    have hdiff : 4 / a - 4 / (a + 1 / 2) = 2 / (a * (a + 1 / 2)) := by
      field_simp
      ring
    have hstep : 1 / a ^ 2 ≤ 4 / a - 4 / (a + 1 / 2) := by
      rw [hdiff]
      apply (div_le_div_iff₀ (sq_pos_of_pos hapos) (mul_pos hapos haypos)).mpr
      nlinarith
    have hcast : r + ((n + 1 : ℕ) : ℝ) / 2 = a + 1 / 2 := by dsimp [a]; push_cast; ring
    rw [hcast]
    change _ ≤ 4 / r - 4 / (a + 1 / 2)
    change _ ≤ 4 / r - 4 / a at ih
    linarith

theorem norm_tsum_le_reciprocal_majorant (f : ℕ → ℂ) (B r : ℝ)
    (hB : 0 ≤ B) (hr : 1 ≤ r) (hs : Summable (fun k => ‖f k‖))
    (hb : ∀ k, ‖f k‖ ≤ B / (r + (k : ℝ) / 2) ^ 2) :
    ‖∑' k, f k‖ ≤ 4 * B / r := by
  have hfinite : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, f k‖ ≤ 4 * B / r := by
    intro n
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖f k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range n, B / (r + (k : ℝ) / 2) ^ 2 := Finset.sum_le_sum (fun k _ => hb k)
      _ = B * ∑ k ∈ Finset.range n, 1 / (r + (k : ℝ) / 2) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ ≤ B * (4 / r - 4 / (r + (n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (sum_range_reciprocal_sq_le r hr n) hB
      _ ≤ 4 * B / r := by
        have hpos : 0 < r + (n : ℝ) / 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have hnonneg : 0 ≤ 4 / (r + (n : ℝ) / 2) := by positivity
        exact (mul_le_mul_of_nonneg_left (sub_le_self _ hnonneg) hB).trans_eq (by ring)
  exact le_of_tendsto hs.of_norm.tendsto_sum_tsum_nat.norm (Eventually.of_forall hfinite)

def attractingCoordinate (u : ℂ) : ℂ :=
  correctedCoordinate parabolicMap ParabolicFatouCoordinate.model
    (coordinateDefect parabolicMap ParabolicFatouCoordinate.model) u

def attractingTail (u : ℂ) : ℂ :=
  ∑' k : ℕ, orbitTerm parabolicMap (coordinateDefect parabolicMap ParabolicFatouCoordinate.model) u k

def attractingInZeta (z : ℂ) : ℂ := attractingCoordinate (inverseCoordinate z)

def attractingTailInZeta (z : ℂ) : ℂ := attractingTail (inverseCoordinate z)

/-- True orbit decay plus the actual quadratic defect gives a vanishing
tail bound in the reciprocal coordinate, without a tail-bound hypothesis. -/
theorem exists_attracting_tail_bound :
    ∃ R B : ℝ, 32 ≤ R ∧ 0 ≤ B ∧
      DifferentiableOn ℂ attractingTail (ParabolicFatouHolomorphic.petal R) ∧
      ∀ u : ℂ, R < (inverseCoordinate u).re →
        ‖attractingTail u‖ ≤ B / (inverseCoordinate u).re := by
  obtain ⟨Rh, Ch, hRh, hCh, hhol, huni, hsum⟩ :=
    ParabolicFatouHolomorphic.exists_holomorphic_attracting_coordinate
  obtain ⟨r, M, hr, hM, hlocal⟩ := ParabolicFatouCoordinate.exists_local_defect_bound
  let R : ℝ := max 32 (max (Rh + 1) (4 / r))
  have hR : 32 ≤ R := le_max_left _ _
  have hRhR : Rh < R := by
    have h : Rh + 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hRr : 4 / r ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  have hmodel : DifferentiableOn ℂ ParabolicFatouCoordinate.model (ParabolicFatouHolomorphic.petal Rh) := by
    intro u hu
    exact (ParabolicFatouHolomorphic.analyticAt_model (by change Rh < _ at hu; linarith)).differentiableAt.differentiableWithinAt
  have htail : DifferentiableOn ℂ attractingTail (ParabolicFatouHolomorphic.petal Rh) := by
    convert hhol.sub hmodel using 1 <;> first | rfl | (funext u; dsimp [attractingTail, correctedCoordinate]; ring)
  refine ⟨R, 16 * M, hR, by positivity, htail.mono (fun u hu => hRhR.trans hu), ?_⟩
  intro u hu
  let t : ℝ := (inverseCoordinate u).re
  have ht32 : 32 ≤ t := hR.trans hu.le
  have ht1 : 1 ≤ t := by linarith
  have htr : 4 / r ≤ t := hRr.trans hu.le
  have hsmall : 2 / t < r := by
    have h := (div_le_iff₀ hr).mp htr
    apply (div_lt_iff₀ (by linarith : 0 < t)).mpr
    nlinarith
  have hb : ∀ k : ℕ,
      ‖orbitTerm parabolicMap (coordinateDefect parabolicMap ParabolicFatouCoordinate.model) u k‖ ≤
        (4 * M) / (t + (k : ℝ) / 2) ^ 2 := by
    intro k
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hnorm := iterate_norm_bound_of_threshold u t ht32 (le_refl _) k
    have hpos : 0 < t + (k : ℝ) / 2 := by linarith
    have hsize : ‖(parabolicMap^[k]) u‖ < r :=
      (hnorm.trans (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))).trans_lt hsmall
    have hp : 0 < (inverseCoordinate ((parabolicMap^[k]) u)).re := by
      have h := iterate_inverse_re u ht32 k
      linarith
    have hd := hlocal ((parabolicMap^[k]) u) hsize hp
    change ‖coordinateDefect parabolicMap ParabolicFatouCoordinate.model ((parabolicMap^[k]) u)‖ ≤ _
    apply hd.trans
    convert mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hM using 1
    field_simp
    ring
  have hs := (hsum u (hRhR.trans hu)).1
  have ht := norm_tsum_le_reciprocal_majorant _ (4 * M) t (by positivity) ht1 hs hb
  simpa only [attractingTail, t, show 4 * (4 * M) = 16 * M by ring] using ht

def zetaModel (sign : ℂ) (z : ℂ) : ℂ := z + sign * Complex.log (2 / z) / 3

theorem attractingInZeta_eq (z : ℂ) :
    attractingInZeta z = zetaModel 1 z + attractingTailInZeta z := by
  have hm : ParabolicFatouCoordinate.model (inverseCoordinate z) = zetaModel 1 z := by
    change inverseCoordinate (inverseCoordinate z) + Complex.log (-inverseCoordinate z) / 3 = _
    rw [inverseCoordinate_involutive]
    have he : -inverseCoordinate z = 2 / z := by dsimp [inverseCoordinate]; ring
    rw [he]
    simp [zetaModel]
  exact congrArg (fun x => x + attractingTailInZeta z) hm

theorem hasDerivAt_inverseCoordinate (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt inverseCoordinate (2 / z ^ 2) z := by
  have h := (hasDerivAt_const z (-2 : ℂ)).div (hasDerivAt_id z) hz
  convert h using 1 <;> first | rfl | (simp; try ring)

theorem hasDerivAt_zetaModel (sign z : ℂ) (hz : 0 < z.re) :
    HasDerivAt (zetaModel sign) (1 - sign / (3 * z)) z := by
  have hzne : z ≠ 0 := by intro he; simp [he] at hz
  have hslit : (2 : ℂ) / z ∈ Complex.slitPlane := by
    have hpos : 0 < (inverseCoordinate (inverseCoordinate z)).re := by
      simpa only [inverseCoordinate_involutive] using hz
    have hp := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hpos
    have he : -inverseCoordinate z = 2 / z := by dsimp [inverseCoordinate]; ring
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by rwa [he] at hp))
  have hd := (hasDerivAt_id z).add
    (((((hasDerivAt_const z (2 : ℂ)).div (hasDerivAt_id z) hzne).clog hslit).const_mul sign).div_const 3)
  change HasDerivAt (zetaModel sign) (1 + sign * ((0 * z - 2 * 1) / z ^ 2 / (2 / z)) / 3) z at hd
  convert hd using 1
  field_simp
  ring

/-- The actual orbit tail is holomorphic and uniformly vanishing on a
right half-plane in the reciprocal coordinate. -/
theorem exists_attracting_zeta_tail_bound :
    ∃ R B : ℝ, 32 ≤ R ∧ 0 ≤ B ∧ DifferentiableOn ℂ attractingTailInZeta (halfPlane R) ∧
      ∀ z ∈ halfPlane R, ‖attractingTailInZeta z‖ ≤ B / z.re := by
  obtain ⟨R, B, hR, hB, hhol, hb⟩ := exists_attracting_tail_bound
  refine ⟨R, B, hR, hB, ?_, ?_⟩
  · intro z hz
    change R < z.re at hz
    have hzne : z ≠ 0 := by intro he; simp [he] at hz; linarith
    have himage : inverseCoordinate z ∈ ParabolicFatouHolomorphic.petal R := by
      change R < (inverseCoordinate (inverseCoordinate z)).re
      rwa [inverseCoordinate_involutive]
    have ha := hhol.analyticAt ((ParabolicFatouHolomorphic.petal_isOpen (by linarith)).mem_nhds himage)
    exact (ha.comp (analyticAt_const.div analyticAt_id hzne)).differentiableAt.differentiableWithinAt
  · intro z hz
    change R < z.re at hz
    have h := hb (inverseCoordinate z) (by simpa only [inverseCoordinate_involutive] using hz)
    simpa only [attractingTailInZeta, inverseCoordinate_involutive] using h

theorem re_lower_bound_on_closedBall (z w : ℂ) (hw : w ∈ closedBall z (z.re / 2)) :
    z.re / 2 ≤ w.re := by
  have hn : ‖z - w‖ ≤ z.re / 2 := by
    simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hw
  have hre := Complex.re_le_norm (z - w)
  simp only [Complex.sub_re] at hre
  linarith

/-- The Cauchy derivative estimate is obtained from the tail bound on an
actual closed disc contained in the right half-plane. -/
theorem norm_deriv_tail_le (T : ℂ → ℂ) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hhol : DifferentiableOn ℂ T (halfPlane R))
    (hb : ∀ z ∈ halfPlane R, ‖T z‖ ≤ B / z.re)
    (z : ℂ) (hz : 2 * R < z.re) : ‖deriv T z‖ ≤ 4 * B / z.re ^ 2 := by
  have hpos : 0 < z.re := by linarith
  have hr : 0 < z.re / 2 := by positivity
  have hdisc : ∀ w ∈ closedBall z (z.re / 2), w ∈ halfPlane R := by
    intro w hw
    have hh := re_lower_bound_on_closedBall z w hw
    change R < w.re
    linarith
  have hd : DifferentiableOn ℂ T (closedBall z (z.re / 2)) := by
    intro w hw
    exact (hhol.analyticAt ((halfPlane_isOpen R).mem_nhds (hdisc w hw))).differentiableAt.differentiableWithinAt
  have hbd : ∀ w ∈ sphere z (z.re / 2), ‖T w‖ ≤ 2 * B / z.re := by
    intro w hw
    have hwc : w ∈ closedBall z (z.re / 2) := mem_closedBall.mpr (mem_sphere.mp hw).le
    have hh := re_lower_bound_on_closedBall z w hwc
    apply (hb w (hdisc w hwc)).trans
    exact (div_le_div_of_nonneg_left hB hr hh).trans_eq (by field_simp; try ring)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    ((hd.mono closure_ball_subset_closedBall).diffContOnCl) hbd
  exact hc.trans_eq (by field_simp; try ring)

theorem analyticAt_zetaModel (sign z : ℂ) (hz : 0 < z.re) :
    AnalyticAt ℂ (zetaModel sign) z := by
  have hzne : z ≠ 0 := by intro he; simp [he] at hz
  have hp := ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos
    (show 0 < (inverseCoordinate (inverseCoordinate z)).re by simpa only [inverseCoordinate_involutive] using hz)
  have he : -inverseCoordinate z = 2 / z := by dsimp [inverseCoordinate]; ring
  have hslit : (2 : ℂ) / z ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by rwa [he] at hp))
  exact analyticAt_id.add (((analyticAt_const.mul
    ((analyticAt_const.div analyticAt_id hzne).clog hslit))).div_const)

theorem norm_model_deriv_sub_one_le (sign z : ℂ) (hsign : ‖sign‖ ≤ 1) (hz : 0 < z.re) :
    ‖deriv (zetaModel sign) z - 1‖ ≤ 1 / (3 * z.re) := by
  rw [(hasDerivAt_zetaModel sign z hz).deriv]
  have he : 1 - sign / (3 * z) - 1 = -(sign / (3 * z)) := by ring
  rw [he, norm_neg, norm_div, norm_mul]
  rw [show ‖(3 : ℂ)‖ = (3 : ℝ) by norm_num]
  have hzn : 0 < ‖z‖ := hz.trans_le (Complex.re_le_norm z)
  calc
    _ ≤ 1 / (3 * ‖z‖) := div_le_div_of_nonneg_right hsign (by positivity)
    _ ≤ 1 / (3 * z.re) := div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (mul_le_mul_of_nonneg_left (Complex.re_le_norm z) (by norm_num))

/-- A proved small derivative deviation on a convex half-plane gives
injectivity; this implication does not assume univalence. -/
theorem injectiveOn_of_deriv_sub_one_le (G : ℂ → ℂ) (R : ℝ)
    (ha : ∀ z ∈ halfPlane R, AnalyticAt ℂ G z)
    (hb : ∀ z ∈ halfPlane R, ‖deriv G z - 1‖ ≤ 1 / 2) :
    InjOn G (halfPlane R) := by
  have hd : ∀ z ∈ halfPlane R, DifferentiableAt ℂ (fun w => G w - w) z :=
    fun z hz => (ha z hz).differentiableAt.sub differentiableAt_id
  have hbd : ∀ z ∈ halfPlane R, ‖deriv (fun w => G w - w) z‖ ≤ 1 / 2 := by
    intro z hz
    have he := ((ha z hz).hasStrictDerivAt.hasDerivAt.sub (hasDerivAt_id z)).deriv
    change deriv (fun w => G w - w) z = deriv G z - 1 at he
    rw [he]
    exact hb z hz
  intro x hx y hy hxy
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le hd hbd (halfPlane_convex R) hx hy
  have he : (G y - y) - (G x - x) = -(y - x) := by rw [hxy]; ring
  rw [he, norm_neg] at hm
  have hz : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

/-- Model and tail estimates imply nonvanishing derivative and univalence
on a deeper half-plane, with all constants chosen before the spatial point. -/
theorem exists_univalent_model_plus_tail (T : ℂ → ℂ) (sign : ℂ)
    (hsign : ‖sign‖ ≤ 1) (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hhol : DifferentiableOn ℂ T (halfPlane R))
    (hb : ∀ z ∈ halfPlane R, ‖T z‖ ≤ B / z.re) :
    ∃ S : ℝ, 2 * R + 1 ≤ S ∧
      (∀ z ∈ halfPlane S, AnalyticAt ℂ (fun w => zetaModel sign w + T w) z ∧
        ‖deriv (fun w => zetaModel sign w + T w) z - 1‖ ≤ 1 / 2 ∧
        deriv (fun w => zetaModel sign w + T w) z ≠ 0) ∧
      InjOn (fun w => zetaModel sign w + T w) (halfPlane S) := by
  let S : ℝ := max (2 * R + 1) (max 4 (16 * B + 1))
  have hS : 2 * R + 1 ≤ S := le_max_left _ _
  have hfour : 4 ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hBsize : 16 * B + 1 ≤ S := (le_max_right _ _).trans (le_max_right _ _)
  have hdata : ∀ z ∈ halfPlane S, AnalyticAt ℂ (fun w => zetaModel sign w + T w) z ∧
      ‖deriv (fun w => zetaModel sign w + T w) z - 1‖ ≤ 1 / 2 ∧
      deriv (fun w => zetaModel sign w + T w) z ≠ 0 := by
    intro z hz
    change S < z.re at hz
    have hpos : 0 < z.re := by linarith
    have hRz : z ∈ halfPlane R := by change R < z.re; linarith
    have hTa := hhol.analyticAt ((halfPlane_isOpen R).mem_nhds hRz)
    have hGa := (analyticAt_zetaModel sign z hpos).add hTa
    have hGd := (hasDerivAt_zetaModel sign z hpos).add hTa.hasStrictDerivAt.hasDerivAt
    change HasDerivAt (fun w => zetaModel sign w + T w) (1 - sign / (3 * z) + deriv T z) z at hGd
    have hlog := norm_model_deriv_sub_one_le sign z hsign hpos
    have htail := norm_deriv_tail_le T R B hR hB hhol hb z (by linarith)
    have hlogsmall : 1 / (3 * z.re) ≤ (1 / 12 : ℝ) := by
      apply (div_le_iff₀ (by positivity : 0 < 3 * z.re)).mpr
      linarith
    have htailsmall : 4 * B / z.re ^ 2 ≤ (1 / 4 : ℝ) := by
      apply (div_le_iff₀ (sq_pos_of_pos hpos)).mpr
      have hmul : 0 ≤ z.re * (z.re - 1) := mul_nonneg hpos.le (by linarith)
      nlinarith
    have hdev : ‖deriv (fun w => zetaModel sign w + T w) z - 1‖ ≤ 1 / 2 := by
      rw [hGd.deriv]
      have he : (1 - sign / (3 * z) + deriv T z) - 1 =
          ((1 - sign / (3 * z)) - 1) + deriv T z := by ring
      rw [he]
      have hm := norm_add_le ((1 - sign / (3 * z)) - 1) (deriv T z)
      rw [← (hasDerivAt_zetaModel sign z hpos).deriv] at hm
      rw [← (hasDerivAt_zetaModel sign z hpos).deriv]
      linarith
    refine ⟨hGa, hdev, ?_⟩
    intro heq
    rw [heq] at hdev
    norm_num at hdev
  refine ⟨S, hS, hdata, ?_⟩
  exact injectiveOn_of_deriv_sub_one_le _ S (fun z hz => (hdata z hz).1)
    (fun z hz => (hdata z hz).2.1)

theorem exists_analytic_local_inverse (f : ℂ → ℂ) (u : ℂ) (ha : AnalyticAt ℂ f u)
    (hd : deriv f u ≠ 0) :
    ∃ I : ℂ → ℂ, AnalyticAt ℂ I (f u) ∧ I (f u) = u ∧
      (∀ᶠ v in 𝓝 u, I (f v) = v) ∧ (∀ᶠ w in 𝓝 (f u), f (I w) = w) := by
  let I := ha.hasStrictDerivAt.localInverse f (deriv f u) u hd
  have hleft := ha.hasStrictDerivAt.eventually_left_inverse hd
  refine ⟨I, ha.analyticAt_localInverse hd, hleft.self_of_nhds, hleft,
    ha.hasStrictDerivAt.eventually_right_inverse hd⟩

def CanonicalJacobian (f : ℂ → ℂ) (R : ℝ) : Prop :=
  InjOn f (ParabolicFatouHolomorphic.petal R) ∧
    ∀ u ∈ ParabolicFatouHolomorphic.petal R, AnalyticAt ℂ f u ∧ deriv f u ≠ 0 ∧
      ∃ I : ℂ → ℂ, AnalyticAt ℂ I (f u) ∧ I (f u) = u ∧
        (∀ᶠ v in 𝓝 u, I (f v) = v) ∧ (∀ᶠ w in 𝓝 (f u), f (I w) = w)

/-- Reciprocal pullback preserves the proved univalence and transports
the nonzero derivative to the actual spatial Fatou coordinate. -/
theorem canonicalJacobian_of_zeta (f : ℂ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (ha : ∀ z ∈ halfPlane R, AnalyticAt ℂ (fun w => f (inverseCoordinate w)) z ∧
      deriv (fun w => f (inverseCoordinate w)) z ≠ 0)
    (hi : InjOn (fun w => f (inverseCoordinate w)) (halfPlane R)) :
    CanonicalJacobian f R := by
  have he : (fun w => f (inverseCoordinate (inverseCoordinate w))) = f := by
    funext w
    rw [inverseCoordinate_involutive]
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    have hui : inverseCoordinate u ∈ halfPlane R := hu
    have hvi : inverseCoordinate v ∈ halfPlane R := hv
    have h := hi hui hvi (by simpa only [inverseCoordinate_involutive] using huv)
    have hh := congrArg inverseCoordinate h
    simpa only [inverseCoordinate_involutive] using hh
  · intro u hu
    have hpos : 0 < (inverseCoordinate u).re := hR.trans_lt hu
    have hune : u ≠ 0 := by intro h; simp [h, inverseCoordinate] at hpos
    have hzne : inverseCoordinate u ≠ 0 := by intro h; simp [h] at hpos
    obtain ⟨hza, hzd⟩ := ha (inverseCoordinate u) hu
    have hfa : AnalyticAt ℂ f u := by
      have h := hza.comp (analyticAt_const.div analyticAt_id hune)
      change AnalyticAt ℂ (fun w => f (inverseCoordinate (inverseCoordinate w))) u at h
      rwa [he] at h
    have hfd : deriv f u ≠ 0 := by
      intro hz
      have hfu : HasDerivAt f (deriv f u) (inverseCoordinate (inverseCoordinate u)) := by
        simpa only [inverseCoordinate_involutive] using hfa.hasStrictDerivAt.hasDerivAt
      have hc := hfu.comp (inverseCoordinate u)
        (hasDerivAt_inverseCoordinate (inverseCoordinate u) hzne)
      have hc' := hc.deriv
      change deriv (fun w => f (inverseCoordinate w)) (inverseCoordinate u) =
        deriv f u * (2 / inverseCoordinate u ^ 2) at hc'
      rw [hz, zero_mul] at hc'
      exact hzd hc'
    exact ⟨hfa, hfd, exists_analytic_local_inverse f u hfa hfd⟩

/-- The canonical attracting coordinate is genuinely univalent and has
a local analytic inverse on a sufficiently deep full petal. -/
theorem exists_attracting_canonicalJacobian :
    ∃ R : ℝ, 32 ≤ R ∧ CanonicalJacobian attractingCoordinate R ∧
      (∀ z ∈ halfPlane R, ‖deriv attractingInZeta z - 1‖ ≤ 1 / 2) := by
  obtain ⟨R, B, hR, hB, hhol, hb⟩ := exists_attracting_zeta_tail_bound
  obtain ⟨S, hS, hdata, hi⟩ := exists_univalent_model_plus_tail attractingTailInZeta 1
    (by norm_num) R B (by linarith) hB hhol hb
  have he : (fun w => zetaModel 1 w + attractingTailInZeta w) = attractingInZeta :=
    funext (fun w => (attractingInZeta_eq w).symm)
  rw [he] at hdata hi
  refine ⟨S, by linarith, ?_, fun z hz => (hdata z hz).2.1⟩
  exact canonicalJacobian_of_zeta attractingCoordinate S (by linarith)
    (fun z hz => ⟨(hdata z hz).1, (hdata z hz).2.2⟩) hi

open Kneser.RepellingExponentialOrbit

def repellingCoordinate (u : ℂ) : ℂ :=
  correctedCoordinate parabolicInverse RepellingFatouCoordinate.model
    (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) u

def repellingTail (u : ℂ) : ℂ :=
  ∑' k : ℕ, orbitTerm parabolicInverse
    (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) u k

def repellingInZeta (z : ℂ) : ℂ := repellingCoordinate (inverseCoordinate z)

def repellingTailInZeta (z : ℂ) : ℂ := repellingTail (inverseCoordinate z)

theorem analyticAt_repelling_model {u : ℂ} (hu : 0 < (inverseCoordinate u).re) :
    AnalyticAt ℂ RepellingFatouCoordinate.model u := by
  have hune : u ≠ 0 := by intro h; simp [h, inverseCoordinate] at hu
  have hslit : -u ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (ParabolicFatouCoordinate.neg_re_pos_of_inverse_re_pos hu))
  exact (analyticAt_const.div analyticAt_id hune).sub
    (((analyticAt_id.neg).clog hslit).div_const)

theorem mapsTo_inverse_iterate_petal {R : ℝ} (hR : 64 ≤ R) (k : ℕ) :
    MapsTo (parabolicInverse^[k]) (ParabolicFatouHolomorphic.petal R)
      (ParabolicFatouHolomorphic.petal R) := by
  intro u hu
  have hk := RepellingFatouCoordinate.inverse_iterate_re u
    (inverseCoordinate u).re (hR.trans hu.le) (le_refl _) k
  change R < (inverseCoordinate ((parabolicInverse^[k]) u)).re
  change R < (inverseCoordinate u).re at hu
  linarith [Nat.cast_nonneg (α := ℝ) k]

theorem differentiableOn_parabolicInverse_petal {R : ℝ} (hR : 64 ≤ R) :
    DifferentiableOn ℂ parabolicInverse (ParabolicFatouHolomorphic.petal R) := by
  intro u hu
  have hpos : 0 < (inverseCoordinate u).re := by change R < _ at hu; linarith
  have hn := Kneser.ParabolicExponentialOrbit.norm_le_two_div_re u hpos
  have hsmall : ‖u‖ < 1 := by
    apply hn.trans_lt
    apply (div_lt_iff₀ hpos).mpr
    change R < _ at hu
    linarith
  exact (hasDerivAt_parabolicInverse u hsmall).differentiableAt.differentiableWithinAt

theorem differentiableOn_repelling_defect_petal {R : ℝ} (hR : 64 ≤ R) :
    DifferentiableOn ℂ (coordinateDefect parabolicInverse RepellingFatouCoordinate.model)
      (ParabolicFatouHolomorphic.petal R) := by
  have hmodel : DifferentiableOn ℂ RepellingFatouCoordinate.model
      (ParabolicFatouHolomorphic.petal R) := by
    intro u hu
    exact (analyticAt_repelling_model (by change R < _ at hu; linarith)).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo parabolicInverse (ParabolicFatouHolomorphic.petal R)
      (ParabolicFatouHolomorphic.petal R) := by
    simpa using mapsTo_inverse_iterate_petal hR 1
  exact ((hmodel.comp (differentiableOn_parabolicInverse_petal hR) hmaps).sub hmodel).sub_const 1

/-- The canonical reflected coordinate is holomorphic on a full petal;
uniform convergence follows from the actual inverse-orbit majorant. -/
theorem exists_holomorphic_repelling_coordinate :
    ∃ R C : ℝ, 64 ≤ R ∧ 0 ≤ C ∧
      DifferentiableOn ℂ repellingCoordinate (ParabolicFatouHolomorphic.petal R) ∧
      DifferentiableOn ℂ repellingTail (ParabolicFatouHolomorphic.petal R) ∧
      TendstoUniformlyOn
        (fun n : ℕ => fun u : ℂ => ∑ k ∈ Finset.range n,
          orbitTerm parabolicInverse (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) u k)
        repellingTail atTop (ParabolicFatouHolomorphic.petal R) ∧
      ∀ u ∈ ParabolicFatouHolomorphic.petal R,
        Summable (fun k => ‖orbitTerm parabolicInverse
          (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) u k‖) ∧
        repellingCoordinate (parabolicInverse u) = repellingCoordinate u + 1 := by
  obtain ⟨R, C, hR, hC, hresult⟩ := RepellingFatouCoordinate.exists_repelling_fatou_coordinate
  have hbound : ∀ k : ℕ, ∀ u ∈ ParabolicFatouHolomorphic.petal R,
      ‖orbitTerm parabolicInverse (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) u k‖ ≤
        C / ((k : ℝ) + 1) ^ 2 := by
    intro k u hu
    exact (hresult u hu.le).1 k
  have hmaps : MapsTo parabolicInverse (ParabolicFatouHolomorphic.petal R)
      (ParabolicFatouHolomorphic.petal R) := by
    simpa using mapsTo_inverse_iterate_petal hR 1
  have hterms : ∀ k : ℕ, DifferentiableOn ℂ
      (fun u => orbitTerm parabolicInverse
        (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) u k)
      (ParabolicFatouHolomorphic.petal R) := by
    intro k
    exact (differentiableOn_repelling_defect_petal hR).comp
      ((differentiableOn_parabolicInverse_petal hR).iterate hmaps k)
      (mapsTo_inverse_iterate_petal hR k)
  have hmodel : DifferentiableOn ℂ RepellingFatouCoordinate.model
      (ParabolicFatouHolomorphic.petal R) := by
    intro u hu
    exact (analyticAt_repelling_model (by change R < _ at hu; linarith)).differentiableAt.differentiableWithinAt
  have hsum := Complex.differentiableOn_tsum_of_summable_norm
    (summable_parabolic_majorant C (by norm_num : 2 ≤ (2 : ℕ))) hterms
    (ParabolicFatouHolomorphic.petal_isOpen (by linarith)) (fun k u hu => hbound k u hu)
  have huni := tendstoUniformlyOn_tsum
    (summable_parabolic_majorant C (by norm_num : 2 ≤ (2 : ℕ))) (fun k u hu => hbound k u hu)
  refine ⟨R, C, hR, hC, hmodel.add hsum, hsum, ?_, ?_⟩
  · intro v hv
    exact (tendsto_finset_range : Tendsto Finset.range atTop atTop).eventually (huni v hv)
  · intro u hu
    exact ⟨(hresult u hu.le).2.1, (hresult u hu.le).2.2.1⟩

theorem exists_repelling_tail_bound :
    ∃ R B : ℝ, 64 ≤ R ∧ 0 ≤ B ∧
      DifferentiableOn ℂ repellingTail (ParabolicFatouHolomorphic.petal R) ∧
      ∀ u : ℂ, R < (inverseCoordinate u).re →
        ‖repellingTail u‖ ≤ B / (inverseCoordinate u).re := by
  obtain ⟨Rh, Ch, hRh, hCh, hhol, htail, huni, hsum⟩ := exists_holomorphic_repelling_coordinate
  obtain ⟨r, M, hr, hM, hlocal⟩ := RepellingFatouCoordinate.exists_local_defect_bound
  let R : ℝ := max 64 (max (Rh + 1) (4 / r))
  have hR : 64 ≤ R := le_max_left _ _
  have hRhR : Rh < R := by
    have h : Rh + 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have hRr : 4 / r ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R, 16 * M, hR, by positivity, htail.mono (fun u hu => hRhR.trans hu), ?_⟩
  intro u hu
  let t : ℝ := (inverseCoordinate u).re
  have ht64 : 64 ≤ t := hR.trans hu.le
  have ht1 : 1 ≤ t := by linarith
  have htr : 4 / r ≤ t := hRr.trans hu.le
  have hsmall : 2 / t < r := by
    have h := (div_le_iff₀ hr).mp htr
    apply (div_lt_iff₀ (by linarith : 0 < t)).mpr
    nlinarith
  have hb : ∀ k : ℕ,
      ‖orbitTerm parabolicInverse (coordinateDefect parabolicInverse RepellingFatouCoordinate.model) u k‖ ≤
        (4 * M) / (t + (k : ℝ) / 2) ^ 2 := by
    intro k
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hnorm := RepellingFatouCoordinate.inverse_iterate_norm_bound u t ht64 (le_refl _) k
    have hpos : 0 < t + (k : ℝ) / 2 := by linarith
    have hsize : ‖(parabolicInverse^[k]) u‖ < r :=
      (hnorm.trans (div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith))).trans_lt hsmall
    have hp : 0 < (inverseCoordinate ((parabolicInverse^[k]) u)).re := by
      have h := RepellingFatouCoordinate.inverse_iterate_re u t ht64 (le_refl _) k
      linarith
    have hd := hlocal ((parabolicInverse^[k]) u) hsize hp
    change ‖coordinateDefect parabolicInverse RepellingFatouCoordinate.model ((parabolicInverse^[k]) u)‖ ≤ _
    apply hd.trans
    convert mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hM using 1
    field_simp
    ring
  have hs := (hsum u (hRhR.trans hu)).1
  have ht := norm_tsum_le_reciprocal_majorant _ (4 * M) t (by positivity) ht1 hs hb
  simpa only [repellingTail, t, show 4 * (4 * M) = 16 * M by ring] using ht

theorem repellingInZeta_eq (z : ℂ) :
    repellingInZeta z = zetaModel (-1) z + repellingTailInZeta z := by
  have hm : RepellingFatouCoordinate.model (inverseCoordinate z) = zetaModel (-1) z := by
    change inverseCoordinate (inverseCoordinate z) - Complex.log (-inverseCoordinate z) / 3 = _
    rw [inverseCoordinate_involutive]
    have he : -inverseCoordinate z = 2 / z := by dsimp [inverseCoordinate]; ring
    rw [he]
    simp [zetaModel]
    ring
  exact congrArg (fun x => x + repellingTailInZeta z) hm

theorem exists_repelling_zeta_tail_bound :
    ∃ R B : ℝ, 64 ≤ R ∧ 0 ≤ B ∧ DifferentiableOn ℂ repellingTailInZeta (halfPlane R) ∧
      ∀ z ∈ halfPlane R, ‖repellingTailInZeta z‖ ≤ B / z.re := by
  obtain ⟨R, B, hR, hB, hhol, hb⟩ := exists_repelling_tail_bound
  refine ⟨R, B, hR, hB, ?_, ?_⟩
  · intro z hz
    change R < z.re at hz
    have hzne : z ≠ 0 := by intro he; simp [he] at hz; linarith
    have himage : inverseCoordinate z ∈ ParabolicFatouHolomorphic.petal R := by
      change R < (inverseCoordinate (inverseCoordinate z)).re
      rwa [inverseCoordinate_involutive]
    have ha := hhol.analyticAt ((ParabolicFatouHolomorphic.petal_isOpen (by linarith)).mem_nhds himage)
    exact (ha.comp (analyticAt_const.div analyticAt_id hzne)).differentiableAt.differentiableWithinAt
  · intro z hz
    change R < z.re at hz
    have h := hb (inverseCoordinate z) (by simpa only [inverseCoordinate_involutive] using hz)
    simpa only [repellingTailInZeta, inverseCoordinate_involutive] using h

/-- The canonical reflected inverse coordinate is genuinely univalent and
has a local analytic inverse on a sufficiently deep full petal. -/
theorem exists_repelling_canonicalJacobian :
    ∃ R : ℝ, 64 ≤ R ∧ CanonicalJacobian repellingCoordinate R ∧
      (∀ z ∈ halfPlane R, ‖deriv repellingInZeta z - 1‖ ≤ 1 / 2) := by
  obtain ⟨R, B, hR, hB, hhol, hb⟩ := exists_repelling_zeta_tail_bound
  obtain ⟨S, hS, hdata, hi⟩ := exists_univalent_model_plus_tail repellingTailInZeta (-1)
    (by norm_num) R B (by linarith) hB hhol hb
  have he : (fun w => zetaModel (-1) w + repellingTailInZeta w) = repellingInZeta :=
    funext (fun w => (repellingInZeta_eq w).symm)
  rw [he] at hdata hi
  refine ⟨S, by linarith, ?_, fun z hz => (hdata z hz).2.1⟩
  exact canonicalJacobian_of_zeta repellingCoordinate S (by linarith)
    (fun z hz => ⟨(hdata z hz).1, (hdata z hz).2.2⟩) hi

/-- One depth works for both actual canonical coordinates. -/
theorem exists_bilateral_canonicalJacobian :
    ∃ R : ℝ, 64 ≤ R ∧ CanonicalJacobian attractingCoordinate R ∧
      CanonicalJacobian repellingCoordinate R := by
  obtain ⟨Ra, hRa, hca, _⟩ := exists_attracting_canonicalJacobian
  obtain ⟨Rr, hRr, hcr, _⟩ := exists_repelling_canonicalJacobian
  let R := max Ra Rr
  have hsuba : ParabolicFatouHolomorphic.petal R ⊆ ParabolicFatouHolomorphic.petal Ra :=
    fun _ hu => (le_max_left Ra Rr).trans_lt hu
  have hsubr : ParabolicFatouHolomorphic.petal R ⊆ ParabolicFatouHolomorphic.petal Rr :=
    fun _ hu => (le_max_right Ra Rr).trans_lt hu
  exact ⟨R, hRr.trans (le_max_right _ _),
    ⟨hca.1.mono hsuba, fun u hu => hca.2 u (hsuba hu)⟩,
    ⟨hcr.1.mono hsubr, fun u hu => hcr.2 u (hsubr hu)⟩⟩

end Kneser.ParabolicCoordinateJacobian

end
