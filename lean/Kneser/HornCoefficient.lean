import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# First-order coefficient of a normalized horn-map Fourier coefficient

This file proves the coefficient-extraction step of the paper. The dynamical
input is explicit: the two Fourier coefficients have the indicated derivatives
at the parabolic parameter. From these hypotheses Lean checks the derivative of
`τₙ`, the derivative of its normalized principal logarithm, and the change from
`s` to a parameter `p` with `ds/dp = 1/2`.

No orbit estimates or existence of the input derivatives are assumed to have
been proved in this file. Integer modes include every positive Fourier mode.
-/

namespace Kneser

open Complex

/-- The frequency `2π i n` of an arbitrary integer Fourier mode. -/
noncomputable def fourierFrequency (n : ℤ) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)

/-- The coordinate-independent coefficient `τₙ = tₙ exp(-2π i n t₀)`. -/
noncomputable def hornCoefficient (n : ℤ) (tn t0 : ℂ → ℂ) (s : ℂ) : ℂ :=
  tn s * Complex.exp (-fourierFrequency n * t0 s)

/-- Normalization at the parabolic parameter. -/
noncomputable def normalizedHornCoefficient (n : ℤ) (tn t0 : ℂ → ℂ) (s : ℂ) : ℂ :=
  hornCoefficient n tn t0 s / hornCoefficient n tn t0 0

/-- The paper's first-order coefficient in the parameter `p = 2s + o(s)`. -/
noncomputable def hornKappa (n : ℤ) (B dtn dt0 : ℂ) : ℂ :=
  dtn / (2 * B) - (Real.pi : ℂ) * Complex.I * (n : ℂ) * dt0

/-- The leading horn coefficient is `Bₙ exp(2π i n a)`. -/
theorem hornCoefficient_zero (n : ℤ) (tn t0 : ℂ → ℂ) (B a : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) :
    hornCoefficient n tn t0 0 = B * Complex.exp (fourierFrequency n * a) := by
  simp [hornCoefficient, htn0, ht00]

/-- A nonzero limiting Fourier coefficient permits normalization. -/
theorem hornCoefficient_zero_ne (n : ℤ) (tn t0 : ℂ → ℂ) (B a : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0) :
    hornCoefficient n tn t0 0 ≠ 0 := by
  rw [hornCoefficient_zero n tn t0 B a htn0 ht00]
  exact mul_ne_zero hB (Complex.exp_ne_zero _)

/-- Differentiation of `τₙ` gives the explicit first-order correction. -/
theorem hasDerivAt_hornCoefficient (n : ℤ) (tn t0 : ℂ → ℂ)
    (B a dtn dt0 : ℂ) (htn0 : tn 0 = B) (ht00 : t0 0 = -a)
    (htn : HasDerivAt tn dtn 0) (ht0 : HasDerivAt t0 dt0 0) :
    HasDerivAt (hornCoefficient n tn t0)
      (Complex.exp (fourierFrequency n * a) *
        (dtn - fourierFrequency n * B * dt0)) 0 := by
  have h := htn.mul ((ht0.const_mul (-fourierFrequency n)).cexp)
  apply h.congr_deriv
  simp only [htn0, ht00, mul_neg, neg_mul, neg_neg]
  ring

/-- The normalized coefficient equals one at the parabolic parameter. -/
theorem normalizedHornCoefficient_zero (n : ℤ) (tn t0 : ℂ → ℂ) (B a : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0) :
    normalizedHornCoefficient n tn t0 0 = 1 := by
  exact div_self (hornCoefficient_zero_ne n tn t0 B a htn0 ht00 hB)

/-- The first derivative in `s` is twice the first coefficient in `p`. -/
theorem hasDerivAt_normalizedHornCoefficient (n : ℤ) (tn t0 : ℂ → ℂ)
    (B a dtn dt0 : ℂ) (htn0 : tn 0 = B) (ht00 : t0 0 = -a)
    (hB : B ≠ 0) (htn : HasDerivAt tn dtn 0) (ht0 : HasDerivAt t0 dt0 0) :
    HasDerivAt (normalizedHornCoefficient n tn t0)
      (2 * hornKappa n B dtn dt0) 0 := by
  have h := (hasDerivAt_hornCoefficient n tn t0 B a dtn dt0 htn0 ht00 htn ht0).div_const
    (hornCoefficient n tn t0 0)
  apply h.congr_deriv
  rw [hornCoefficient_zero n tn t0 B a htn0 ht00]
  unfold hornKappa fourierFrequency
  field_simp [hB, Complex.exp_ne_zero]

/-- The principal complex logarithm is differentiable at the normalized value
`1`, so its derivative is the same explicit coefficient `2κₙ`. -/
theorem hasDerivAt_log_normalizedHornCoefficient (n : ℤ) (tn t0 : ℂ → ℂ)
    (B a dtn dt0 : ℂ) (htn0 : tn 0 = B) (ht00 : t0 0 = -a)
    (hB : B ≠ 0) (htn : HasDerivAt tn dtn 0) (ht0 : HasDerivAt t0 dt0 0) :
    HasDerivAt (fun s => Complex.log (normalizedHornCoefficient n tn t0 s))
      (2 * hornKappa n B dtn dt0) 0 := by
  have hnorm := normalizedHornCoefficient_zero n tn t0 B a htn0 ht00 hB
  have h := (hasDerivAt_normalizedHornCoefficient n tn t0 B a dtn dt0
    htn0 ht00 hB htn ht0).clog (by rw [hnorm]; exact Complex.one_mem_slitPlane)
  simpa only [hnorm, div_one] using h

/-- A differentiable change of parameter with `ds/dp = 1/2` gives exactly the
paper's coefficient `κₙ = δtₙ/(2Bₙ) - π i n δt₀`. -/
theorem hasDerivAt_log_normalizedHornCoefficient_reparam (n : ℤ)
    (tn t0 sOfP : ℂ → ℂ) (B a dtn dt0 : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0)
    (htn : HasDerivAt tn dtn 0) (ht0 : HasDerivAt t0 dt0 0)
    (hs0 : sOfP 0 = 0) (hs : HasDerivAt sOfP (1 / 2) 0) :
    HasDerivAt (fun p => Complex.log (normalizedHornCoefficient n tn t0 (sOfP p)))
      (hornKappa n B dtn dt0) 0 := by
  have h : HasDerivAt (fun s => Complex.log (normalizedHornCoefficient n tn t0 s))
      (2 * hornKappa n B dtn dt0) (sOfP 0) := by
    simpa only [hs0] using hasDerivAt_log_normalizedHornCoefficient n tn t0 B a dtn dt0
      htn0 ht00 hB htn ht0
  apply (h.comp 0 hs).congr_deriv
  ring

/-- The normalized principal logarithm vanishes at the parabolic parameter. -/
theorem log_normalizedHornCoefficient_zero (n : ℤ) (tn t0 : ℂ → ℂ)
    (B a : ℂ) (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0) :
    Complex.log (normalizedHornCoefficient n tn t0 0) = 0 := by
  rw [normalizedHornCoefficient_zero n tn t0 B a htn0 ht00 hB, Complex.log_one]

/-- Equivalent coefficient extraction using the forward parameter derivative
`dp/ds = 2`, without choosing an inverse change of parameter. -/
theorem deriv_log_div_deriv_parameter_eq_hornKappa (n : ℤ)
    (tn t0 pOfS : ℂ → ℂ) (B a dtn dt0 : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0)
    (htn : HasDerivAt tn dtn 0) (ht0 : HasDerivAt t0 dt0 0)
    (hp : HasDerivAt pOfS 2 0) :
    deriv (fun s => Complex.log (normalizedHornCoefficient n tn t0 s)) 0 /
      deriv pOfS 0 = hornKappa n B dtn dt0 := by
  rw [(hasDerivAt_log_normalizedHornCoefficient n tn t0 B a dtn dt0
    htn0 ht00 hB htn ht0).deriv, hp.deriv]
  ring

/-! ## One-sided real parameter

These lemmas require only the right derivatives established by the orbit
estimates. In particular, they require no extension that is complex
differentiable at the parabolic parameter.
-/

/-- The same horn coefficient, now with a real unfolding parameter. -/
noncomputable def realHornCoefficient (n : ℤ) (tn t0 : ℝ → ℂ) (s : ℝ) : ℂ :=
  tn s * Complex.exp (-fourierFrequency n * t0 s)

/-- Normalized horn coefficient for the real unfolding parameter. -/
noncomputable def realNormalizedHornCoefficient (n : ℤ) (tn t0 : ℝ → ℂ) (s : ℝ) : ℂ :=
  realHornCoefficient n tn t0 s / realHornCoefficient n tn t0 0

/-- The limiting value follows from the values of the real-parameter inputs. -/
theorem realHornCoefficient_zero (n : ℤ) (tn t0 : ℝ → ℂ) (B a : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) :
    realHornCoefficient n tn t0 0 = B * Complex.exp (fourierFrequency n * a) := by
  simp [realHornCoefficient, htn0, ht00]

/-- Nonvanishing at zero makes the real-parameter normalization valid. -/
theorem realHornCoefficient_zero_ne (n : ℤ) (tn t0 : ℝ → ℂ) (B a : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0) :
    realHornCoefficient n tn t0 0 ≠ 0 := by
  rw [realHornCoefficient_zero n tn t0 B a htn0 ht00]
  exact mul_ne_zero hB (Complex.exp_ne_zero _)

/-- The real-parameter normalization equals one at zero. -/
theorem realNormalizedHornCoefficient_zero (n : ℤ) (tn t0 : ℝ → ℂ) (B a : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0) :
    realNormalizedHornCoefficient n tn t0 0 = 1 := by
  exact div_self (realHornCoefficient_zero_ne n tn t0 B a htn0 ht00 hB)

/-- The derivative calculation works within any specified real parameter set. -/
theorem hasDerivWithinAt_realHornCoefficient (n : ℤ) (tn t0 : ℝ → ℂ)
    (S : Set ℝ) (B a dtn dt0 : ℂ) (htn0 : tn 0 = B) (ht00 : t0 0 = -a)
    (htn : HasDerivWithinAt tn dtn S 0) (ht0 : HasDerivWithinAt t0 dt0 S 0) :
    HasDerivWithinAt (realHornCoefficient n tn t0)
      (Complex.exp (fourierFrequency n * a) *
        (dtn - fourierFrequency n * B * dt0)) S 0 := by
  have h := htn.mul ((ht0.const_mul (-fourierFrequency n)).cexp)
  apply h.congr_deriv
  simp only [htn0, ht00, mul_neg, neg_mul, neg_neg]
  ring

/-- The normalized first-order coefficient calculation needs only derivatives
within the real parameter set. -/
theorem hasDerivWithinAt_realNormalizedHornCoefficient (n : ℤ) (tn t0 : ℝ → ℂ)
    (S : Set ℝ) (B a dtn dt0 : ℂ) (htn0 : tn 0 = B) (ht00 : t0 0 = -a)
    (hB : B ≠ 0) (htn : HasDerivWithinAt tn dtn S 0)
    (ht0 : HasDerivWithinAt t0 dt0 S 0) :
    HasDerivWithinAt (realNormalizedHornCoefficient n tn t0)
      (2 * hornKappa n B dtn dt0) S 0 := by
  have h := (hasDerivWithinAt_realHornCoefficient n tn t0 S B a dtn dt0
    htn0 ht00 htn ht0).div_const (realHornCoefficient n tn t0 0)
  apply h.congr_deriv
  rw [realHornCoefficient_zero n tn t0 B a htn0 ht00]
  unfold hornKappa fourierFrequency
  field_simp [hB, Complex.exp_ne_zero]

/-- The principal-log correction needs only derivatives within a real set. -/
theorem hasDerivWithinAt_log_realNormalizedHornCoefficient (n : ℤ) (tn t0 : ℝ → ℂ)
    (S : Set ℝ) (B a dtn dt0 : ℂ) (htn0 : tn 0 = B) (ht00 : t0 0 = -a)
    (hB : B ≠ 0) (htn : HasDerivWithinAt tn dtn S 0)
    (ht0 : HasDerivWithinAt t0 dt0 S 0) :
    HasDerivWithinAt (fun s => Complex.log (realNormalizedHornCoefficient n tn t0 s))
      (2 * hornKappa n B dtn dt0) S 0 := by
  have hnorm := realNormalizedHornCoefficient_zero n tn t0 B a htn0 ht00 hB
  have h := (hasDerivWithinAt_realNormalizedHornCoefficient n tn t0 S B a dtn dt0
    htn0 ht00 hB htn ht0).clog_real
    (by rw [hnorm]; exact Complex.one_mem_slitPlane)
  simpa only [hnorm, div_one] using h

/-- The paper's actual one-sided first correction, for `s → 0+`. -/
theorem hasDerivWithinAt_log_realNormalizedHornCoefficient_right (n : ℤ)
    (tn t0 : ℝ → ℂ) (B a dtn dt0 : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0)
    (htn : HasDerivWithinAt tn dtn (Set.Ici 0) 0)
    (ht0 : HasDerivWithinAt t0 dt0 (Set.Ici 0) 0) :
    HasDerivWithinAt (fun s => Complex.log (realNormalizedHornCoefficient n tn t0 s))
      (2 * hornKappa n B dtn dt0) (Set.Ici 0) 0 :=
  hasDerivWithinAt_log_realNormalizedHornCoefficient n tn t0 (Set.Ici 0)
    B a dtn dt0 htn0 ht00 hB htn ht0

/-- With `dp/ds = 2` from the right, the right derivative ratio is exactly the
explicit coefficient `κₙ`. -/
theorem rightDeriv_log_div_rightDeriv_parameter_eq_hornKappa (n : ℤ)
    (tn t0 : ℝ → ℂ) (pOfS : ℝ → ℝ) (B a dtn dt0 : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0)
    (htn : HasDerivWithinAt tn dtn (Set.Ici 0) 0)
    (ht0 : HasDerivWithinAt t0 dt0 (Set.Ici 0) 0)
    (hp : HasDerivWithinAt pOfS 2 (Set.Ici 0) 0) :
    derivWithin (fun s => Complex.log (realNormalizedHornCoefficient n tn t0 s))
        (Set.Ici 0) 0 / ((derivWithin pOfS (Set.Ici 0) 0 : ℝ) : ℂ) =
      hornKappa n B dtn dt0 := by
  rw [(hasDerivWithinAt_log_realNormalizedHornCoefficient_right n tn t0 B a dtn dt0
    htn0 ht00 hB htn ht0).derivWithin (uniqueDiffWithinAt_Ici 0),
    hp.derivWithin (uniqueDiffWithinAt_Ici 0)]
  norm_num

/-- An actual right-sided change of parameter preserves the calculated
coefficient when it maps nonnegative parameters to nonnegative parameters. -/
theorem hasDerivWithinAt_log_realNormalizedHornCoefficient_right_reparam (n : ℤ)
    (tn t0 : ℝ → ℂ) (sOfP : ℝ → ℝ) (B a dtn dt0 : ℂ)
    (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0)
    (htn : HasDerivWithinAt tn dtn (Set.Ici 0) 0)
    (ht0 : HasDerivWithinAt t0 dt0 (Set.Ici 0) 0)
    (hs0 : sOfP 0 = 0) (hs : HasDerivWithinAt sOfP (1 / 2) (Set.Ici 0) 0)
    (hsMaps : Set.MapsTo sOfP (Set.Ici 0) (Set.Ici 0)) :
    HasDerivWithinAt
      (fun p => Complex.log (realNormalizedHornCoefficient n tn t0 (sOfP p)))
      (hornKappa n B dtn dt0) (Set.Ici 0) 0 := by
  have h : HasDerivWithinAt
      (fun s => Complex.log (realNormalizedHornCoefficient n tn t0 s))
      (2 * hornKappa n B dtn dt0) (Set.Ici 0) (sOfP 0) := by
    simpa only [hs0] using
      hasDerivWithinAt_log_realNormalizedHornCoefficient_right n tn t0 B a dtn dt0
        htn0 ht00 hB htn ht0
  apply (h.scomp 0 hs hsMaps).congr_deriv
  simp [Complex.real_smul]

/-- The real-parameter logarithm has zero constant coefficient. -/
theorem log_realNormalizedHornCoefficient_zero (n : ℤ) (tn t0 : ℝ → ℂ)
    (B a : ℂ) (htn0 : tn 0 = B) (ht00 : t0 0 = -a) (hB : B ≠ 0) :
    Complex.log (realNormalizedHornCoefficient n tn t0 0) = 0 := by
  rw [realNormalizedHornCoefficient_zero n tn t0 B a htn0 ht00 hB, Complex.log_one]

end Kneser
