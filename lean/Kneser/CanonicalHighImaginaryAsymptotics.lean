import Kneser.ParabolicNonrealDefect
import Kneser.HighImaginaryOrbit

/-! Actual global canonical Fatou coordinates approach their logarithmic
models at large reciprocal imaginary height. Finite orbit defects are
bounded using the true nonreal analytic continuation, and the remaining
infinite tail is bounded at the genuine deep endpoint. -/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace Kneser.CanonicalHighImaginaryAsymptotics

open Filter Set Metric Complex Kneser.ParabolicExponentialOrbit
open Kneser.ParabolicFatouCoordinate Kneser.RepellingExponentialOrbit
open Kneser.ParabolicCoordinateJacobian Kneser.ParabolicFatouHolomorphic
open Kneser.CanonicalBasinExtension Kneser.FatouBasinExtension
open Kneser.ParabolicNonrealDefect Kneser.HighImaginaryOrbit
open scoped Topology BigOperators

theorem log_upper_branch (u : ℂ) (hu : 0 < u.im) :
    Complex.log u = Complex.log (-u) + (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp only [Complex.log_re, Complex.add_re, norm_neg, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero]
  · simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
    rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hu]
    ring

def upperRepelling (R : ℝ) (u : ℂ) : ℂ := globalRepelling R u - (Real.pi : ℂ) * I / 3

theorem physical_model_eq_upper (u : ℂ) (hu : 0 < u.im) :
    -RepellingFatouCoordinate.model (-u) =
      ParabolicFatouCoordinate.model u + (Real.pi : ℂ) * I / 3 := by
  simp only [RepellingFatouCoordinate.model, ParabolicFatouCoordinate.model, neg_neg, div_neg]
  rw [log_upper_branch u hu]
  ring

theorem model_defect_sum (f Ψ : ℂ → ℂ) (u : ℂ) (N : ℕ) :
    Ψ ((f^[N]) u) - Ψ u - (N : ℂ) =
      ∑ k ∈ Finset.range N, coordinateDefect f Ψ ((f^[k]) u) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ← ih, Function.iterate_succ_apply']
    simp only [coordinateDefect, Nat.cast_add, Nat.cast_one]
    ring

theorem finite_orbit_im_ne_zero (f : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (u : ℂ) (N : ℕ) (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (k : ℕ) (hk : k ≤ N) : ((f^[k]) u).im ≠ 0 := by
  intro he
  have hi : (inverseCoordinate ((f^[k]) u)).im = 0 := by
    simp [inverseCoordinate, Complex.div_im, he]
  have hb := ParabolicOverlapGate.finite_orbit_gate_bound f hstep u N hg k hk
  have hh := (Complex.abs_im_le_norm
    (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ)))).trans hb
  simp only [Complex.sub_im, hi, Complex.add_im, Complex.natCast_im, add_zero,
    zero_sub, abs_neg] at hh
  have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem finite_orbit_re_lower (f : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (u : ℂ) (N : ℕ) (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (hRe : |(inverseCoordinate u).re| ≤ 64) :
    3 * (N : ℝ) / 4 - 64 ≤ (inverseCoordinate ((f^[N]) u)).re := by
  have hb := ParabolicOverlapGate.finite_orbit_gate_bound f hstep u N hg N le_rfl
  have hh := (Complex.abs_re_le_norm
    (inverseCoordinate ((f^[N]) u) - (inverseCoordinate u + (N : ℂ)))).trans hb
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re] at hh
  have ha := (abs_le.mp hh).1
  have hinit := (abs_le.mp hRe).1
  linarith

theorem nonreal_finite_defect_sum_bound (f Ψ : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (r C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ v : ℂ, ‖v‖ < r → v.im ≠ 0 → ‖coordinateDefect f Ψ v‖ ≤ C * ‖v‖ ^ 2)
    (u : ℂ) (N : ℕ) (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (hr : 4 / |(inverseCoordinate u).im| < r) :
    ‖∑ k ∈ Finset.range N, coordinateDefect f Ψ ((f^[k]) u)‖ ≤
      (N : ℝ) * C * (4 / |(inverseCoordinate u).im|) ^ 2 := by
  calc
    _ ≤ ∑ k ∈ Finset.range N, ‖coordinateDefect f Ψ ((f^[k]) u)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, C * (4 / |(inverseCoordinate u).im|) ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      have hkN := Nat.le_of_lt (Finset.mem_range.mp hk)
      have hn := finite_orbit_height_norm f hstep u N hg k hkN
      exact (hD _ (hn.trans_lt hr) (finite_orbit_im_ne_zero f hstep u N hg k hkN)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 2) hC)
    _ = _ := by simp; ring

theorem finite_transport_error_bound (f φ Ψ : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (r C B : ℝ) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hD : ∀ v : ℂ, ‖v‖ < r → v.im ≠ 0 → ‖coordinateDefect f Ψ v‖ ≤ C * ‖v‖ ^ 2)
    (u : ℂ) (N : ℕ) (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (hRe : |(inverseCoordinate u).re| ≤ 64) (hr : 4 / |(inverseCoordinate u).im| < r)
    (hpos : 0 < 3 * (N : ℝ) / 4 - 64)
    (htail : ‖φ ((f^[N]) u) - Ψ ((f^[N]) u)‖ ≤ B / (inverseCoordinate ((f^[N]) u)).re) :
    ‖transport f φ N u - Ψ u‖ ≤
      B / (3 * (N : ℝ) / 4 - 64) + (N : ℝ) * C * (4 / |(inverseCoordinate u).im|) ^ 2 := by
  have he : transport f φ N u - Ψ u =
      (φ ((f^[N]) u) - Ψ ((f^[N]) u)) +
        ∑ k ∈ Finset.range N, coordinateDefect f Ψ ((f^[k]) u) := by
    rw [← model_defect_sum]
    dsimp [transport]
    ring
  rw [he]
  have hh := finite_orbit_re_lower f hstep u N hg hRe
  exact (norm_add_le _ _).trans (add_le_add
    (htail.trans (div_le_div_of_nonneg_left hB hpos hh))
    (nonreal_finite_defect_sum_bound f Ψ hstep r C hC hD u N hg hr))

theorem globalAttracting_finite_error (R Rt r C B : ℝ) (hs : CanonicalSeedData R)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hD : ∀ v : ℂ, ‖v‖ < r → v.im ≠ 0 →
      ‖coordinateDefect parabolicMap ParabolicFatouCoordinate.model v‖ ≤ C * ‖v‖ ^ 2)
    (hT : ∀ v : ℂ, Rt < (inverseCoordinate v).re → ‖attractingTail v‖ ≤ B / (inverseCoordinate v).re)
    (u : ℂ) (N : ℕ) (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (hRe : |(inverseCoordinate u).re| ≤ 64) (hr : 4 / |(inverseCoordinate u).im| < r)
    (hR : R < 3 * (N : ℝ) / 4 - 64) (hRt : Rt < 3 * (N : ℝ) / 4 - 64) :
    ‖globalAttracting R u - ParabolicFatouCoordinate.model u‖ ≤
      B / (3 * (N : ℝ) / 4 - 64) + (N : ℝ) * C * (4 / |(inverseCoordinate u).im|) ^ 2 := by
  have hp := finite_orbit_re_lower parabolicMap inverse_step_error_bound u N hg hRe
  have hentry : Entry parabolicMap (petal R) u N :=
    ⟨hR.trans_le hp, iterate_analytic_jacobian _ parabolicMap_analytic_jacobian u N⟩
  rw [globalAttracting, extend_eq_transport _ _ _ hs.attracting_map hs.attracting_abel u N hentry]
  apply finite_transport_error_bound parabolicMap attractingCoordinate ParabolicFatouCoordinate.model
    inverse_step_error_bound r C B hC hB hD u N hg hRe hr (by linarith [hs.depth])
  have ht := hT ((parabolicMap^[N]) u) (hRt.trans_le hp)
  simpa only [attractingCoordinate, attractingTail, correctedCoordinate, add_sub_cancel_left] using ht

theorem globalReflected_finite_error (R Rt r C B : ℝ) (hs : CanonicalSeedData R)
    (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hD : ∀ v : ℂ, ‖v‖ < r → v.im ≠ 0 →
      ‖coordinateDefect parabolicInverse RepellingFatouCoordinate.model v‖ ≤ C * ‖v‖ ^ 2)
    (hT : ∀ v : ℂ, Rt < (inverseCoordinate v).re → ‖repellingTail v‖ ≤ B / (inverseCoordinate v).re)
    (v : ℂ) (N : ℕ) (hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate v).im|)
    (hRe : |(inverseCoordinate v).re| ≤ 64) (hr : 4 / |(inverseCoordinate v).im| < r)
    (hR : R < 3 * (N : ℝ) / 4 - 64) (hRt : Rt < 3 * (N : ℝ) / 4 - 64) :
    ‖globalReflected R v - RepellingFatouCoordinate.model v‖ ≤
      B / (3 * (N : ℝ) / 4 - 64) + (N : ℝ) * C * (4 / |(inverseCoordinate v).im|) ^ 2 := by
  have hp := finite_orbit_re_lower parabolicInverse RepellingExponentialOrbit.inverse_step_error_bound v N hg hRe
  have hentry : Entry parabolicInverse (petal R) v N := by
    have hp' : (parabolicInverse^[N]) v ∈ petal R := hR.trans_le hp
    have he := CanonicalBasinExtension.inverse_gate_entry R N (-v) (by
      simpa only [neg_neg, RepellingFatouCoordinate.inverseOrbit_zero_parameter] using hp') (by
        simpa only [neg_neg] using hg)
    simpa only [neg_neg] using he
  rw [globalReflected, extend_eq_transport _ _ _ hs.repelling_map hs.repelling_abel v N hentry]
  apply finite_transport_error_bound parabolicInverse repellingCoordinate RepellingFatouCoordinate.model
    RepellingExponentialOrbit.inverse_step_error_bound r C B hC hB hD v N hg hRe hr (by linarith [hs.depth])
  have ht := hT ((parabolicInverse^[N]) v) (hRt.trans_le hp)
  simpa only [repellingCoordinate, repellingTail, correctedCoordinate, add_sub_cancel_left] using ht


theorem height_error_bound (Y D t C B : ℝ) (hY : 0 < Y) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (ht : 0 ≤ t) (htY : t ≤ Y / 128) (hD : Y / 1024 ≤ D) :
    B / D + t * C * (4 / Y) ^ 2 ≤ (1024 * B + C) / Y := by
  have hd : 0 < Y / 1024 := by positivity
  have hfirst : B / D ≤ 1024 * B / Y := by
    have h := div_le_div_of_nonneg_left hB hd hD
    convert h using 1 <;> first | rfl | (field_simp <;> ring)
  have hlast : t * C * (4 / Y) ^ 2 ≤ C / Y := by
    calc
      _ ≤ (Y / 128) * C * (4 / Y) ^ 2 := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htY hC) (sq_nonneg _)
      _ = C / (8 * Y) := by field_simp <;> ring
      _ ≤ C / Y := div_le_div_of_nonneg_left hC hY (by linarith)
  exact (add_le_add hfirst hlast).trans_eq (by ring)

/-- Both global coordinates are the actual canonical ones. The complete
large-height error is `O(1/|Im ζ|)`, uniformly for bounded `Re ζ`.
No global comparison or horn normalization hypothesis is an input. -/
theorem exists_global_model_bounds (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₀ Ca Cr : ℝ, 0 < Y₀ ∧ 0 ≤ Ca ∧ 0 ≤ Cr ∧ ∀ u : ℂ,
      |(inverseCoordinate u).re| ≤ 64 → Y₀ < |(inverseCoordinate u).im| →
      ‖globalAttracting R u - ParabolicFatouCoordinate.model u‖ ≤ Ca / |(inverseCoordinate u).im| ∧
      ‖globalRepelling R u - (-RepellingFatouCoordinate.model (-u))‖ ≤ Cr / |(inverseCoordinate u).im| := by
  obtain ⟨ra, Da, hra, hDa, hdefa⟩ := exists_forward_nonreal_defect_bound
  obtain ⟨rr, Dr, hrr, hDr, hdefr⟩ := exists_inverse_nonreal_defect_bound
  obtain ⟨Ra, Ba, _hRa, hBa, _hha, htaila⟩ := exists_attracting_tail_bound
  obtain ⟨Rr, Br, _hRr, hBr, _hhr, htailr⟩ := exists_repelling_tail_bound
  let r : ℝ := min ra rr
  have hr : 0 < r := lt_min hra hrr
  let X : ℝ := max R (max Ra Rr)
  let Y₀ : ℝ := max 32768 (max (1024 * (X + 1)) (8 / r))
  have hY₀ : 0 < Y₀ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 32768) (le_max_left _ _)
  refine ⟨Y₀, 1024 * Ba + Da, 1024 * Br + Dr, hY₀, by positivity, by positivity, ?_⟩
  intro u hRe hheight
  let Y : ℝ := |(inverseCoordinate u).im|
  have hY : 0 < Y := hY₀.trans hheight
  have hYbig : 32768 < Y := (le_max_left _ _).trans_lt hheight
  have hYX : 1024 * (X + 1) < Y :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hheight
  have hYr : 8 / r < Y :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hheight
  let N : ℕ := Nat.floor (Y / 128)
  have hNu : (N : ℝ) ≤ Y / 128 := Nat.floor_le (by positivity)
  have hNl : Y / 128 - 1 < (N : ℝ) := Nat.sub_one_lt_floor _
  have hgate : 64 * ((N : ℝ) + 1) ≤ Y := by linarith
  have hden : Y / 1024 ≤ 3 * (N : ℝ) / 4 - 64 := by linarith
  have hRX : R ≤ X := le_max_left _ _
  have hRaX : Ra ≤ X := (le_max_left _ _).trans (le_max_right _ _)
  have hRrX : Rr ≤ X := (le_max_right _ _).trans (le_max_right _ _)
  have hdeep : X < 3 * (N : ℝ) / 4 - 64 := by linarith
  have hsmall : 4 / Y < r := by
    apply (div_lt_iff₀ hY).mpr
    have hh := (div_lt_iff₀ hr).mp hYr
    nlinarith
  have hsmallA : 4 / Y < ra := hsmall.trans_le (min_le_left _ _)
  have hsmallR : 4 / Y < rr := hsmall.trans_le (min_le_right _ _)
  have hA := globalAttracting_finite_error R Ra ra Da Ba hs hDa hBa hdefa htaila u N
    hgate hRe hsmallA (hRX.trans_lt hdeep) (hRaX.trans_lt hdeep)
  have hinv : inverseCoordinate (-u) = -inverseCoordinate u := by
    simp only [inverseCoordinate, div_neg]
  have hR := globalReflected_finite_error R Rr rr Dr Br hs hDr hBr hdefr htailr (-u) N
    (by simpa only [hinv, Complex.neg_im, abs_neg] using hgate)
    (by simpa only [hinv, Complex.neg_re, abs_neg] using hRe)
    (by simpa only [hinv, Complex.neg_im, abs_neg] using hsmallR)
    (hRX.trans_lt hdeep) (hRrX.trans_lt hdeep)
  constructor
  · exact hA.trans (height_error_bound Y _ (N : ℝ) Da Ba hY hDa hBa
      (Nat.cast_nonneg _) hNu hden)
  · have he : globalRepelling R u - (-RepellingFatouCoordinate.model (-u)) =
        -(globalReflected R (-u) - RepellingFatouCoordinate.model (-u)) := by
      dsimp [globalRepelling]
      ring
    rw [he, norm_neg]
    have hh : ‖globalReflected R (-u) - RepellingFatouCoordinate.model (-u)‖ ≤
        Br / (3 * (N : ℝ) / 4 - 64) + (N : ℝ) * Dr * (4 / Y) ^ 2 := by
      simpa only [hinv, Complex.neg_im, abs_neg] using hR
    exact hh.trans (height_error_bound Y _ (N : ℝ) Dr Br hY hDr hBr
      (Nat.cast_nonneg _) hNu hden)

theorem exists_upper_normalized_difference_bound (R : ℝ) (hs : CanonicalSeedData R) :
    ∃ Y₀ C : ℝ, 0 < Y₀ ∧ 0 ≤ C ∧ ∀ u : ℂ,
      |(inverseCoordinate u).re| ≤ 64 → 0 < u.im → Y₀ < |(inverseCoordinate u).im| →
      ‖globalAttracting R u - upperRepelling R u‖ ≤ C / |(inverseCoordinate u).im| := by
  obtain ⟨Y₀, Ca, Cr, hY, hCa, hCr, hb⟩ := exists_global_model_bounds R hs
  refine ⟨Y₀, Ca + Cr, hY, by positivity, ?_⟩
  intro u hRe hu hheight
  obtain ⟨ha, hr⟩ := hb u hRe hheight
  have he : globalAttracting R u - upperRepelling R u =
      (globalAttracting R u - ParabolicFatouCoordinate.model u) -
        (globalRepelling R u - (-RepellingFatouCoordinate.model (-u))) := by
    rw [physical_model_eq_upper u hu]
    dsimp [upperRepelling]
    ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add ha hr).trans_eq (by ring))

end Kneser.CanonicalHighImaginaryAsymptotics
end
