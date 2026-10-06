import Kneser.ReflectedPreparedFirstOrder

/-!
# The actual reflected prepared model one-step identity

The reflected logarithmic model is expressed with the original multiplier
residues. The exact exponential factorization then identifies its inverse
one-step defect with the original prepared residual at the inverse image.
-/

noncomputable section

namespace Kneser.ReflectedPreparedModel

open Kneser.ExponentialModelTime Kneser.ExponentialPreparedModel
open Kneser.ExponentialMatrixDividedDifference Kneser.ExponentialUnfolding
open Kneser.ExponentialPreparedQuadratic
open Kneser.AnalyticEvenDescent Kneser.RepellingExponentialOrbit
open Kneser.ParabolicFatouCoordinate (log_mul_of_re_pos)
open scoped Topology

theorem raw_preparedModelTime_residue_pair (U H e₁ e₂ : ℂ → ℂ)
    (x u : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0) :
    preparedModelTime U H e₁ e₂ (x ^ 2) u =
      Complex.log (U x - u) / (x * H x) +
      Complex.log (U (-x) - u) / ((-x) * H (-x)) +
      polynomialCorrection e₁ e₂ (x ^ 2) u := by
  have heven : ∀ z, dslope (fun z => modelNumerator U H z u) 0 (-z) =
      dslope (fun z => modelNumerator U H z u) 0 z :=
    dslope_odd_even (modelNumerator_zero U H u) (fun z => modelNumerator_odd U H z u)
  unfold preparedModelTime logarithmicModel
  rw [even_sqrt_square heven x, dslope_of_ne _ hx, slope_def_field, modelNumerator_zero]
  unfold modelNumerator
  field_simp [hx, hHx, hHnx]
  ring

theorem reflected_preparedModelTime_residue_pair (U H e₁ e₂ : ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x v : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0) :
    preparedModelTime (-U) (-H) e₁ (-e₂) (x ^ 2) v =
      -Complex.log (-U x - v) / Complex.log (rootMultiplier U x) -
      Complex.log (-U (-x) - v) / Complex.log (rootMultiplier U (-x)) -
      polynomialCorrection e₁ e₂ (x ^ 2) (-v) := by
  rw [raw_preparedModelTime_residue_pair (-U) (-H) e₁ (-e₂) x v hx
    (by simpa using hHx) (by simpa using hHnx), hH x, hH (-x)]
  simp only [Pi.neg_apply]
  unfold polynomialCorrection
  simp only [Pi.neg_apply]
  field_simp [hx, hHx, hHnx]
  ring

set_option maxHeartbeats 1000000 in
/-- With explicit local branch conditions, the true reflected inverse's
prepared model defect is the actual original prepared residual evaluated at
its inverse image. No one-step identity is assumed. -/
theorem reflected_preparedModelTime_one_step (U H e₁ e₂ : ℂ → ℂ)
    (hH : ∀ x, Complex.log (rootMultiplier U x) = x * H x)
    (x v F : ℂ) (hx : x ≠ 0) (hHx : H x ≠ 0) (hHnx : H (-x) ≠ 0)
    (hs : x ^ 2 ≠ 1) (hv : ‖v‖ < 1)
    (hf : unfolding (x ^ 2) (-reflectedInverse (x ^ 2) v) + reflectedInverse (x ^ 2) v =
      rootProduct U x (-reflectedInverse (x ^ 2) v) *
        symmetricCofactor U x (-reflectedInverse (x ^ 2) v))
    (hF : F =
      Complex.log (1 + (-reflectedInverse (x ^ 2) v - U (-x)) *
        symmetricCofactor U x (-reflectedInverse (x ^ 2) v)) /
        Complex.log (rootMultiplier U x) +
      Complex.log (1 + (-reflectedInverse (x ^ 2) v - U x) *
        symmetricCofactor U x (-reflectedInverse (x ^ 2) v)) /
        Complex.log (rootMultiplier U (-x)) - 1)
    (ha : 0 < (-U x - reflectedInverse (x ^ 2) v).re)
    (hb : 0 < (-U (-x) - reflectedInverse (x ^ 2) v).re)
    (hra : 0 < (1 + (-reflectedInverse (x ^ 2) v - U (-x)) *
      symmetricCofactor U x (-reflectedInverse (x ^ 2) v)).re)
    (hrb : 0 < (1 + (-reflectedInverse (x ^ 2) v - U x) *
      symmetricCofactor U x (-reflectedInverse (x ^ 2) v)).re) :
    preparedModelTime (-U) (-H) e₁ (-e₂) (x ^ 2) (reflectedInverse (x ^ 2) v) -
      preparedModelTime (-U) (-H) e₁ (-e₂) (x ^ 2) v - 1 =
      F + polynomialCorrection e₁ e₂ (x ^ 2) (-v) -
        polynomialCorrection e₁ e₂ (x ^ 2) (-reflectedInverse (x ^ 2) v) := by
  let w := reflectedInverse (x ^ 2) v
  have hinv : unfolding (x ^ 2) (-w) = -v := unfolding_reflectedInverse _ _ hs hv
  have hpa : -U x - v = (-U x - w) *
      (1 + (-w - U (-x)) * symmetricCofactor U x (-w)) := by
    change unfolding (x ^ 2) (-w) + w = rootProduct U x (-w) * symmetricCofactor U x (-w) at hf
    rw [hinv] at hf
    dsimp [rootProduct] at hf
    linear_combination hf
  have hpb : -U (-x) - v = (-U (-x) - w) *
      (1 + (-w - U x) * symmetricCofactor U x (-w)) := by
    change unfolding (x ^ 2) (-w) + w = rootProduct U x (-w) * symmetricCofactor U x (-w) at hf
    rw [hinv] at hf
    dsimp [rootProduct] at hf
    linear_combination hf
  have hla : Complex.log (-U x - v) - Complex.log (-U x - w) =
      Complex.log (1 + (-w - U (-x)) * symmetricCofactor U x (-w)) := by
    rw [hpa, log_mul_of_re_pos ha hra]
    ring
  have hlb : Complex.log (-U (-x) - v) - Complex.log (-U (-x) - w) =
      Complex.log (1 + (-w - U x) * symmetricCofactor U x (-w)) := by
    rw [hpb, log_mul_of_re_pos hb hrb]
    ring
  rw [reflected_preparedModelTime_residue_pair U H e₁ e₂ hH x _ hx hHx hHnx,
    reflected_preparedModelTime_residue_pair U H e₁ e₂ hH x _ hx hHx hHnx]
  change _ = F + polynomialCorrection e₁ e₂ (x ^ 2) (-v) - polynomialCorrection e₁ e₂ (x ^ 2) (-w)
  linear_combination (1 / Complex.log (rootMultiplier U x)) * hla +
    (1 / Complex.log (rootMultiplier U (-x))) * hlb - hF

end Kneser.ReflectedPreparedModel

end
