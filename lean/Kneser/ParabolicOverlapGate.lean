import Kneser.ParabolicExponentialOrbit
import Kneser.RepellingExponentialOrbit
import Kneser.ReflectedOrbitChainCoefficient

/-!
An actual overlap gate for the parabolic exponential and its principal inverse.
Finite orbit entry is proved from the genuine inverse-coordinate step bound;
it is not an assumed basin or gate-containment condition.
-/

noncomputable section

namespace Kneser.ParabolicOverlapGate

open Kneser.ParabolicExponentialOrbit
open scoped Topology

theorem inverseCoordinate_involutive (u : ℂ) :
    inverseCoordinate (inverseCoordinate u) = u := by
  simp [inverseCoordinate]

theorem norm_small_of_inverse_norm (u : ℂ) (h : 64 ≤ ‖inverseCoordinate u‖) :
    ‖u‖ ≤ 1 / 32 := by
  have hu : u ≠ 0 := by intro hzero; simp [hzero, inverseCoordinate] at h; linarith
  have hup := norm_pos_iff.mpr hu
  rw [inverseCoordinate_norm] at h
  have hm := (le_div_iff₀ hup).mp h
  linarith

/-- A high imaginary gate has controlled genuine finite orbits for either
of the two parabolic maps. The hypothesis here is a local one-step estimate,
which is discharged for both actual maps below. -/
theorem finite_orbit_gate_bound (f : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (u : ℂ) (N : ℕ) (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|) :
    ∀ k : ℕ, k ≤ N →
      ‖inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ))‖ ≤ (k : ℝ) / 4 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k hk =>
    intro hkN
    have hk0 := hk (by omega)
    have hkN' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show k ≤ N by omega)
    have heIm := (Complex.abs_im_le_norm
      (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ)))).trans hk0
    simp only [Complex.sub_im, Complex.add_im, Complex.natCast_im, add_zero] at heIm
    have hi := norm_sub_norm_le (inverseCoordinate u).im
      (inverseCoordinate ((f^[k]) u)).im
    simp only [Real.norm_eq_abs] at hi
    rw [abs_sub_comm] at hi
    have hg : 64 ≤ ‖inverseCoordinate ((f^[k]) u)‖ := by
      have hab := Complex.abs_im_le_norm (inverseCoordinate ((f^[k]) u))
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hn := norm_small_of_inverse_norm ((f^[k]) u) hg
    have hne : (f^[k]) u ≠ 0 := by
      intro hz
      simp [hz, inverseCoordinate] at hg
      linarith
    have hs := hstep ((f^[k]) u) (by linarith) hne
    have heq : inverseCoordinate ((f^[k + 1]) u) -
        (inverseCoordinate u + ((k + 1 : ℕ) : ℂ)) =
        (inverseCoordinate (f ((f^[k]) u)) - inverseCoordinate ((f^[k]) u) - 1) +
        (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ))) := by
      rw [Function.iterate_succ_apply']
      push_cast
      ring
    rw [heq]
    have ht := norm_add_le
      (inverseCoordinate (f ((f^[k]) u)) - inverseCoordinate ((f^[k]) u) - 1)
      (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ)))
    push_cast
    linarith

theorem finite_orbit_gate_norm (f : ℂ → ℂ)
    (hstep : ∀ u : ℂ, ‖u‖ ≤ 1 / 2 → u ≠ 0 →
      ‖inverseCoordinate (f u) - inverseCoordinate u - 1‖ ≤ 8 * ‖u‖)
    (u : ℂ) (N : ℕ) (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|)
    (k : ℕ) (hk : k ≤ N) : ‖(f^[k]) u‖ ≤ 1 / 32 := by
  have hb := finite_orbit_gate_bound f hstep u N hgate k hk
  have hi := (Complex.abs_im_le_norm
    (inverseCoordinate ((f^[k]) u) - (inverseCoordinate u + (k : ℂ)))).trans hb
  simp only [Complex.sub_im, Complex.add_im, Complex.natCast_im, add_zero] at hi
  have ht := norm_sub_norm_le (inverseCoordinate u).im
    (inverseCoordinate ((f^[k]) u)).im
  simp only [Real.norm_eq_abs] at ht
  rw [abs_sub_comm] at ht
  have hn := Complex.abs_im_le_norm (inverseCoordinate ((f^[k]) u))
  have hk' : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hk
  apply norm_small_of_inverse_norm
  linarith [Nat.cast_nonneg (α := ℝ) N]

theorem analyticAt_forward_orbit_joint (u s : ℂ) (k : ℕ) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => ExponentialUnfolding.orbit p.2 p.1 k) (s, u) := by
  induction k with
  | zero => exact analyticAt_snd
  | succ k ih =>
    exact ((analyticAt_fst.neg.add ((analyticAt_const.sub analyticAt_fst).mul ih)).cexp).sub
      analyticAt_const

theorem analyticAt_inverse_orbit_joint_of_gate (v : ℂ) (N : ℕ)
    (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate v).im|) :
    ∀ k : ℕ, k ≤ N →
      AnalyticAt ℂ (fun p : ℂ × ℂ => RepellingExponentialOrbit.inverseOrbit p.2 p.1 k) (0, v) := by
  intro k
  induction k with
  | zero => intro _; exact analyticAt_snd
  | succ k ih =>
    intro hkN
    have hprev := ih (by omega)
    have hn := finite_orbit_gate_norm RepellingExponentialOrbit.parabolicInverse
      RepellingExponentialOrbit.inverse_step_error_bound v N hgate k (by omega)
    have hzero : RepellingExponentialOrbit.inverseOrbit v 0 k =
        (RepellingExponentialOrbit.parabolicInverse^[k]) v := by
      have hf : RepellingExponentialOrbit.reflectedInverse 0 =
          RepellingExponentialOrbit.parabolicInverse :=
        funext RepellingExponentialOrbit.reflectedInverse_zero
      rw [RepellingExponentialOrbit.inverseOrbit, hf]
    have hslit : 1 - RepellingExponentialOrbit.inverseOrbit v 0 k ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr
      left
      simp only [Complex.sub_re, Complex.one_re]
      rw [← hzero] at hn
      linarith [Complex.re_le_norm (RepellingExponentialOrbit.inverseOrbit v 0 k)]
    have h := (((analyticAt_const.sub hprev).clog hslit).add analyticAt_fst).neg.div
      (analyticAt_const.sub analyticAt_fst) (by norm_num : (1 : ℂ) - (0 : ℂ) ≠ 0)
    convert h using 1 <;>
      first | rfl | (funext p; rw [RepellingExponentialOrbit.inverseOrbit_succ]; rfl)

theorem hasDerivAt_inverse_orbit_parameter_of_gate (v : ℂ) (N : ℕ)
    (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate v).im|) :
    ∀ k : ℕ, k ≤ N →
      HasDerivAt (fun s => RepellingExponentialOrbit.inverseOrbit v s k)
        (ReflectedOrbitChainCoefficient.inverseOrbitTangent v k) 0 := by
  intro k
  induction k with
  | zero => intro _; exact hasDerivAt_const 0 v
  | succ k ih =>
    intro hkN
    have hn := finite_orbit_gate_norm RepellingExponentialOrbit.parabolicInverse
      RepellingExponentialOrbit.inverse_step_error_bound v N hgate k (by omega)
    have hzero : RepellingExponentialOrbit.inverseOrbit v 0 k =
        (RepellingExponentialOrbit.parabolicInverse^[k]) v := by
      have hf : RepellingExponentialOrbit.reflectedInverse 0 =
          RepellingExponentialOrbit.parabolicInverse :=
        funext RepellingExponentialOrbit.reflectedInverse_zero
      rw [RepellingExponentialOrbit.inverseOrbit, hf]
    rw [← hzero] at hn
    have hd := ReflectedOrbitChainCoefficient.hasDerivAt_reflectedInverse_curve
      (ih (by omega)) (by linarith : ‖RepellingExponentialOrbit.inverseOrbit v 0 k‖ < 1)
    simpa only [← RepellingExponentialOrbit.inverseOrbit_succ,
      ReflectedOrbitChainCoefficient.inverseOrbitTangent] using hd

/-- The forward orbit reaches an arbitrary deep attracting petal from an
explicit high imaginary gate. -/
theorem attracting_entry (u : ℂ) (N : ℕ) (R : ℝ)
    (hre : -1 ≤ (inverseCoordinate u).re)
    (hN : R + 1 ≤ 3 * (N : ℝ) / 4)
    (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|) :
    R ≤ (inverseCoordinate ((parabolicMap^[N]) u)).re := by
  have h := finite_orbit_gate_bound parabolicMap inverse_step_error_bound u N hgate N le_rfl
  have hr := (Complex.abs_re_le_norm
    (inverseCoordinate ((parabolicMap^[N]) u) - (inverseCoordinate u + (N : ℂ)))).trans h
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re] at hr
  have hl := (abs_le.mp hr).1
  linarith

/-- Reflection puts the genuine backward branch in an attracting petal.
Both entries therefore hold on the same gate of the original u coordinate. -/
theorem repelling_entry (u : ℂ) (N : ℕ) (R : ℝ)
    (hre : (inverseCoordinate u).re ≤ 1)
    (hN : R + 1 ≤ 3 * (N : ℝ) / 4)
    (hgate : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate u).im|) :
    R ≤ (inverseCoordinate ((RepellingExponentialOrbit.parabolicInverse^[N]) (-u))).re := by
  have hneg : inverseCoordinate (-u) = -inverseCoordinate u := by
    simp only [inverseCoordinate, div_neg]
  have hg : 64 * ((N : ℝ) + 1) ≤ |(inverseCoordinate (-u)).im| := by
    simpa [hneg] using hgate
  have h := finite_orbit_gate_bound RepellingExponentialOrbit.parabolicInverse
    RepellingExponentialOrbit.inverse_step_error_bound (-u) N hg N le_rfl
  have hr := (Complex.abs_re_le_norm
    (inverseCoordinate ((RepellingExponentialOrbit.parabolicInverse^[N]) (-u)) -
      (inverseCoordinate (-u) + (N : ℂ)))).trans h
  simp only [hneg, Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.natCast_re] at hr
  have hl := (abs_le.mp hr).1
  linarith

/-- The explicit overlap gate is nonempty for every chosen finite length. -/
theorem exists_gate_point (N : ℕ) :
    ∃ u : ℂ, (inverseCoordinate u).re = 0 ∧
      64 * ((N : ℝ) + 1) < (inverseCoordinate u).im := by
  let Y : ℝ := 64 * ((N : ℝ) + 1) + 1
  refine ⟨inverseCoordinate (Complex.I * (Y : ℂ)), ?_, ?_⟩
  · rw [inverseCoordinate_involutive]
    simp
  · rw [inverseCoordinate_involutive]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    dsimp [Y]
    linarith

end Kneser.ParabolicOverlapGate

end
