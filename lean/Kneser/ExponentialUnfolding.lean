import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The actual exponential unfolding and its finite orbit tangents

This module formalizes the explicit family from the paper's first-order section,
`f_s(u) = exp (-s + (1-s)u) - 1`.  All derivative statements concern the
actual complex exponential and actual finite iterates.  No estimate about
infinite orbits, Fatou coordinates, or horn maps is assumed or proved here.
-/

noncomputable section

namespace Kneser.ExponentialUnfolding

/-- The saddle-node unfolding, with the parabolic parameter at zero. -/
def unfolding (s u : ℂ) : ℂ := Complex.exp (-s + (1 - s) * u) - 1

@[simp] theorem unfolding_zero (u : ℂ) :
    unfolding 0 u = Complex.exp u - 1 := by
  simp [unfolding]

/-- The spatial derivative for every complex parameter. -/
theorem hasDerivAt_unfolding_spatial (s u : ℂ) :
    HasDerivAt (unfolding s)
      (Complex.exp (-s + (1 - s) * u) * (1 - s)) u := by
  change HasDerivAt (fun v : ℂ => Complex.exp (-s + (1 - s) * v) - 1)
    (Complex.exp (-s + (1 - s) * u) * (1 - s)) u
  convert ((((hasDerivAt_id u).const_mul (1 - s)).const_add (-s)).cexp.sub_const 1)
    using 1 <;> first | rfl | (dsimp; ring)

/-- The parameter derivative with the spatial point held fixed. -/
theorem hasDerivAt_unfolding_parameter (s u : ℂ) :
    HasDerivAt (fun t : ℂ => unfolding t u)
      (-(1 + u) * Complex.exp (-s + (1 - s) * u)) s := by
  have h := (((hasDerivAt_id s).neg).add
    (((hasDerivAt_id s).const_sub 1).mul_const u)).cexp.sub_const 1
  convert h using 1 <;> first | rfl | ((try dsimp [unfolding]); ring)

/-- A finite orbit starting at a point independent of the parameter. -/
def orbit (u s : ℂ) : ℕ → ℂ
  | 0 => u
  | k + 1 => unfolding s (orbit u s k)

@[simp] theorem orbit_zero (u s : ℂ) : orbit u s 0 = u := rfl

@[simp] theorem orbit_succ (u s : ℂ) (k : ℕ) :
    orbit u s (k + 1) = unfolding s (orbit u s k) := rfl

/-- The recursively computed parameter tangent at the parabolic parameter. -/
def orbitTangent (u : ℂ) : ℕ → ℂ
  | 0 => 0
  | k + 1 => Complex.exp (orbit u 0 k) * orbitTangent u k -
      (1 + orbit u 0 k) * Complex.exp (orbit u 0 k)

@[simp] theorem orbitTangent_zero (u : ℂ) : orbitTangent u 0 = 0 := rfl

@[simp] theorem orbitTangent_succ (u : ℂ) (k : ℕ) :
    orbitTangent u (k + 1) =
      Complex.exp (orbit u 0 k) * orbitTangent u k -
      (1 + orbit u 0 k) * Complex.exp (orbit u 0 k) := rfl

/-- The tangent recurrence computes the genuine derivative of every finite orbit. -/
theorem hasDerivAt_orbit_parameter_zero (u : ℂ) (k : ℕ) :
    HasDerivAt (fun s : ℂ => orbit u s k) (orbitTangent u k) 0 := by
  induction k with
  | zero => simpa only [orbit_zero, orbitTangent_zero] using hasDerivAt_const 0 u
  | succ k hk =>
    have h := (((hasDerivAt_id (0 : ℂ)).neg).add
      (((hasDerivAt_id (0 : ℂ)).const_sub 1).mul hk)).cexp.sub_const 1
    convert h using 1 <;> first | rfl | skip
    simp only [orbitTangent_succ]
    dsimp
    simp only [neg_zero, sub_zero, one_mul, zero_add]
    ring

/-- The ordinary derivative notation agrees with the explicit recurrence. -/
theorem deriv_orbit_parameter_zero (u : ℂ) (k : ℕ) :
    deriv (fun s : ℂ => orbit u s k) 0 = orbitTangent u k :=
  (hasDerivAt_orbit_parameter_zero u k).deriv

/-- The chain-rule recurrence written directly in terms of actual derivatives. -/
theorem deriv_orbit_parameter_zero_succ (u : ℂ) (k : ℕ) :
    deriv (fun s : ℂ => orbit u s (k + 1)) 0 =
      Complex.exp (orbit u 0 k) * deriv (fun s : ℂ => orbit u s k) 0 -
      (1 + orbit u 0 k) * Complex.exp (orbit u 0 k) := by
  rw [deriv_orbit_parameter_zero, deriv_orbit_parameter_zero, orbitTangent_succ]

/-- The product of spatial derivatives along the parabolic finite orbit. -/
def orbitJacobian (u : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => Complex.exp (orbit u 0 k) * orbitJacobian u k

@[simp] theorem orbitJacobian_zero (u : ℂ) : orbitJacobian u 0 = 1 := rfl

@[simp] theorem orbitJacobian_succ (u : ℂ) (k : ℕ) :
    orbitJacobian u (k + 1) = Complex.exp (orbit u 0 k) * orbitJacobian u k := rfl

/-- All finite spatial derivative products are nonzero. -/
theorem orbitJacobian_ne_zero (u : ℂ) (k : ℕ) : orbitJacobian u k ≠ 0 := by
  induction k with
  | zero => simp only [orbitJacobian_zero, ne_eq, one_ne_zero, not_false_eq_true]
  | succ k hk =>
    exact mul_ne_zero (Complex.exp_ne_zero _) hk

/-- The Jacobian product is the genuine derivative with respect to the initial point. -/
theorem hasDerivAt_orbit_spatial_zero (u : ℂ) (k : ℕ) :
    HasDerivAt (fun w : ℂ => orbit w 0 k) (orbitJacobian u k) u := by
  induction k with
  | zero => convert hasDerivAt_id u using 1 <;> rfl
  | succ k hk =>
    convert (hasDerivAt_unfolding_spatial 0 (orbit u 0 k)).comp u hk using 1 <;>
      first | rfl | (simp only [orbitJacobian_succ, neg_zero, zero_add,
        sub_zero, mul_one, one_mul])

/-- Variation of constants gives an explicit finite sum for the actual orbit tangent. -/
theorem orbitTangent_eq_finite_sum (u : ℂ) (k : ℕ) :
    orbitTangent u k = -orbitJacobian u k *
      (Finset.range k).sum (fun i => (1 + orbit u 0 i) / orbitJacobian u i) := by
  induction k with
  | zero => simp only [orbitTangent_zero, orbitJacobian_zero, Finset.range_zero,
      Finset.sum_empty, mul_zero]
  | succ k hk =>
    rw [orbitTangent_succ, orbitJacobian_succ, Finset.sum_range_succ, hk]
    field_simp [orbitJacobian_ne_zero u k]
    ring

/-- The finite-sum expression evaluates the genuine parameter derivative. -/
theorem deriv_orbit_parameter_zero_eq_finite_sum (u : ℂ) (k : ℕ) :
    deriv (fun s : ℂ => orbit u s k) 0 = -orbitJacobian u k *
      (Finset.range k).sum (fun i => (1 + orbit u 0 i) / orbitJacobian u i) := by
  rw [deriv_orbit_parameter_zero, orbitTangent_eq_finite_sum]

end Kneser.ExponentialUnfolding

end
