import Kneser.ParabolicExponentialOrbit
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.Liouville

/-!
# Finite perturbed orbits of the actual exponential unfolding

The estimates concern `exp (-s + (1-s)u) - 1`, not an abstract map with an
assumed perturbation bound. They are derived from the complex exponential
remainder bound and the numerical petal proved in `ParabolicExponentialOrbit`.
-/

namespace Kneser.PerturbedExponentialOrbit

open ParabolicExponentialOrbit ExponentialUnfolding

/-- On the half-unit disc, the actual exponential unfolding differs from its
parabolic germ by at most `6 |s|` for `|s| ≤ 1/4`. -/
theorem map_perturbation_bound (s u : ℂ) (hu : ‖u‖ ≤ 1 / 2) (hs : ‖s‖ ≤ 1 / 4) :
    ‖unfolding s u - parabolicMap u‖ ≤ 6 * ‖s‖ := by
  have hunorm : ‖u‖ ≤ 1 := by linarith
  have he := Complex.norm_exp_sub_one_le hunorm
  have htri := norm_add_le (Complex.exp u - 1) (1 : ℂ)
  have hexp : ‖Complex.exp u‖ ≤ 2 := by
    have heq : Complex.exp u - 1 + 1 = Complex.exp u := by ring
    rw [heq] at htri
    norm_num at htri
    linarith
  have hplus : ‖(1 : ℂ) + u‖ ≤ 3 / 2 := by
    have hp := norm_add_le (1 : ℂ) u
    norm_num at hp
    linarith
  have harg : ‖-s * (1 + u)‖ ≤ 1 := by
    rw [Complex.norm_mul, norm_neg]
    have hm := mul_le_mul hs hplus (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith
  have hearg := Complex.norm_exp_sub_one_le harg
  have hformula : unfolding s u - parabolicMap u =
      Complex.exp u * (Complex.exp (-s * (1 + u)) - 1) := by
    have ha : -s + (1 - s) * u = u + -s * (1 + u) := by ring
    simp only [unfolding, parabolicMap, ha, Complex.exp_add]
    ring
  rw [hformula, Complex.norm_mul]
  have hm := mul_le_mul hexp hearg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  rw [Complex.norm_mul, norm_neg] at hm
  have hp := mul_le_mul_of_nonneg_left hplus (norm_nonneg s)
  nlinarith

/-- The actual perturbed map remains bounded below if its absolute perturbation
is at most a quarter of the original coordinate. -/
theorem perturbed_map_norm_lower (s u : ℂ) (hu : ‖u‖ ≤ 1 / 2)
    (hs : ‖s‖ ≤ 1 / 4) (hsmall : 6 * ‖s‖ ≤ ‖u‖ / 4) :
    ‖u‖ / 4 ≤ ‖unfolding s u‖ := by
  have hp := map_perturbation_bound s u hu hs
  have hf := map_norm_lower u hu
  have ht := norm_sub_norm_le (parabolicMap u) (unfolding s u)
  rw [norm_sub_rev] at ht
  linarith

/-- The inverse coordinates of the true perturbed and unperturbed maps differ
by at most `24 |s| |ζ|²`. -/
theorem inverse_perturbation_bound (s u : ℂ) (hu : ‖u‖ ≤ 1 / 2)
    (hs : ‖s‖ ≤ 1 / 4) (hne : u ≠ 0) (hsmall : 6 * ‖s‖ ≤ ‖u‖ / 4) :
    ‖inverseCoordinate (unfolding s u) - inverseCoordinate (parabolicMap u)‖ ≤
      24 * ‖s‖ * ‖inverseCoordinate u‖ ^ 2 := by
  have hfne := map_ne_zero u hu hne
  have hupr := norm_pos_iff.mpr hne
  have hlow := perturbed_map_norm_lower s u hu hs hsmall
  have hspos : 0 < ‖unfolding s u‖ := by linarith
  have hsne := norm_pos_iff.mp hspos
  have hfpos := norm_pos_iff.mpr hfne
  have hformula : inverseCoordinate (unfolding s u) - inverseCoordinate (parabolicMap u) =
      2 * (unfolding s u - parabolicMap u) / (unfolding s u * parabolicMap u) := by
    dsimp [inverseCoordinate]
    field_simp
    ring
  rw [hformula, Complex.norm_div, Complex.norm_mul, Complex.norm_mul]
  norm_num
  apply (div_le_iff₀ (mul_pos hspos hfpos)).mpr
  have hpert := map_perturbation_bound s u hu hs
  have hf := map_norm_lower u hu
  have hden : ‖u‖ ^ 2 / 8 ≤ ‖unfolding s u‖ * ‖parabolicMap u‖ := by
    have hm := mul_le_mul hlow hf (by positivity : (0 : ℝ) ≤ ‖u‖ / 2)
      (norm_nonneg _)
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ 24 * ‖s‖ * ‖inverseCoordinate u‖ ^ 2 by positivity)
  have hc : (24 * ‖s‖ * ‖inverseCoordinate u‖ ^ 2) * (‖u‖ ^ 2 / 8) = 12 * ‖s‖ := by
    rw [inverseCoordinate_norm]
    field_simp
    ring
  rw [hc] at hm
  rw [inverseCoordinate_norm] at hm
  nlinarith

/-- A fully numerical local perturbation criterion for an inverse-coordinate
step, derived for the actual exponential maps. -/
theorem inverse_step_bound (s u : ℂ) (hpetal : 64 ≤ (inverseCoordinate u).re)
    (hs : ‖s‖ ≤ 1 / 4)
    (hparam : 24 * ‖s‖ * ‖inverseCoordinate u‖ ^ 2 ≤ 1 / 4) :
    ‖inverseCoordinate (unfolding s u) - inverseCoordinate u - 1‖ ≤ 1 / 2 := by
  have hpos : 0 < (inverseCoordinate u).re := by linarith
  have hn := norm_le_two_div_re u hpos
  have hu : ‖u‖ ≤ 1 / 32 := by
    exact hn.trans ((div_le_iff₀ hpos).mpr (by linarith))
  have hne : u ≠ 0 := by
    intro hz
    simp [hz, inverseCoordinate] at hpos
  have hunorm := norm_pos_iff.mpr hne
  have hζ : 64 ≤ ‖inverseCoordinate u‖ := hpetal.trans (Complex.re_le_norm _)
  have hζpos : 0 < ‖inverseCoordinate u‖ := by linarith
  have hζsquare : ‖inverseCoordinate u‖ ≤ ‖inverseCoordinate u‖ ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hζsquare (norm_nonneg s)
  have hrel : 6 * ‖s‖ * ‖inverseCoordinate u‖ ≤ 1 / 2 := by nlinarith
  have hsmall : 6 * ‖s‖ ≤ ‖u‖ / 4 := by
    rw [inverseCoordinate_norm] at hrel
    have hm := mul_le_mul_of_nonneg_right hrel (le_of_lt hunorm)
    have hc : 6 * ‖s‖ * (2 / ‖u‖) * ‖u‖ = 12 * ‖s‖ := by
      field_simp
      ring
    rw [hc] at hm
    linarith
  have hp := inverse_perturbation_bound s u (by linarith) hs hne hsmall
  have hbase := inverse_step_error_bound u (by linarith) hne
  have heq : inverseCoordinate (unfolding s u) - inverseCoordinate u - 1 =
      (inverseCoordinate (unfolding s u) - inverseCoordinate (parabolicMap u)) +
      (inverseCoordinate (parabolicMap u) - inverseCoordinate u - 1) := by ring
  rw [heq]
  have ht := norm_add_le
    (inverseCoordinate (unfolding s u) - inverseCoordinate (parabolicMap u))
    (inverseCoordinate (parabolicMap u) - inverseCoordinate u - 1)
  linarith

/-- A numerical parameter radius of the required order `J⁻²`. -/
noncomputable def parameterRadius (Z : ℝ) (J : ℕ) : ℝ :=
  1 / (96 * (Z + 2) ^ 2 * ((J : ℝ) + 1) ^ 2)

theorem parameterRadius_pos (Z : ℝ) (hZ : 0 ≤ Z) (J : ℕ) :
    0 < parameterRadius Z J := by
  dsimp [parameterRadius]
  positivity

theorem parameterRadius_le_quarter (Z : ℝ) (hZ : 0 ≤ Z) (J : ℕ) :
    parameterRadius Z J ≤ 1 / 4 := by
  have hB : 2 ≤ Z + 2 := by linarith
  have hm : 1 ≤ (J : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) J]
  have hBsq : 4 ≤ (Z + 2) ^ 2 := by nlinarith
  have hmsq : 1 ≤ ((J : ℝ) + 1) ^ 2 := by nlinarith
  have hp := mul_le_mul hBsq hmsq (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (Z + 2) ^ 2)
  dsimp [parameterRadius]
  apply (div_le_iff₀ (by positivity : 0 < 96 * (Z + 2) ^ 2 * ((J : ℝ) + 1) ^ 2)).mpr
  nlinarith

/-- Enlarging the inverse-coordinate upper bound shrinks the parameter disc. -/
theorem parameterRadius_antitone (Z₁ Z₂ : ℝ) (hZ₁ : 0 ≤ Z₁)
    (hZ : Z₁ ≤ Z₂) (J : ℕ) : parameterRadius Z₂ J ≤ parameterRadius Z₁ J := by
  have hsq : (Z₁ + 2) ^ 2 ≤ (Z₂ + 2) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  dsimp [parameterRadius]
  apply div_le_div_of_nonneg_left (by norm_num)
    (by positivity : 0 < 96 * (Z₁ + 2) ^ 2 * ((J : ℝ) + 1) ^ 2)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
    (by positivity)

/-- The chosen radius controls every inverse coordinate below its finite-orbit
upper bound. -/
theorem local_parameter_bound (Z : ℝ) (hZ : 0 ≤ Z) (J : ℕ) (s z : ℂ)
    (hs : ‖s‖ ≤ parameterRadius Z J)
    (hz : ‖z‖ ≤ (Z + 2) * ((J : ℝ) + 1)) :
    24 * ‖s‖ * ‖z‖ ^ 2 ≤ 1 / 4 := by
  have hsq : ‖z‖ ^ 2 ≤ ((Z + 2) * ((J : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hm := mul_le_mul hs hsq (pow_nonneg (norm_nonneg z) 2)
    (le_of_lt (parameterRadius_pos Z hZ J))
  have hc : parameterRadius Z J * ((Z + 2) * ((J : ℝ) + 1)) ^ 2 = 1 / 96 := by
    dsimp [parameterRadius]
    field_simp
  rw [hc] at hm
  nlinarith

/-- Elementary consequences of a half-unit bound on a translated coordinate
step. The main finite-orbit theorem derives this premise for the actual map. -/
theorem coordinate_increment_bounds (z z' : ℂ) (hstep : ‖z' - z - 1‖ ≤ 1 / 2) :
    z.re + 1 / 2 ≤ z'.re ∧ ‖z'‖ ≤ ‖z‖ + 2 := by
  have hreal := (abs_le.mp ((Complex.abs_re_le_norm (z' - z - 1)).trans hstep)).1
  simp only [Complex.sub_re, Complex.one_re] at hreal
  constructor
  · linarith
  · have heq : z' = z + 1 + (z' - z - 1) := by ring
    have ht1 := norm_add_le z (1 : ℂ)
    have ht2 := norm_add_le (z + 1) (z' - z - 1)
    have hn : ‖z'‖ = ‖z + 1 + (z' - z - 1)‖ := congrArg norm heq
    norm_num at ht1
    linarith

/-- Genuine perturbed finite orbits remain in the petal for complex parameters
inside an explicitly computed disc. Both real-part growth and norm growth are
proved by induction on the actual exponential orbit. -/
theorem finite_orbit_inverse_bounds (u s : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (J : ℕ)
    (hs : ‖s‖ ≤ parameterRadius ‖inverseCoordinate u‖ J)
    (k : ℕ) (hk : k ≤ J) :
    R + (k : ℝ) / 2 ≤ (inverseCoordinate (orbit u s k)).re ∧
      ‖inverseCoordinate (orbit u s k)‖ ≤ ‖inverseCoordinate u‖ + 2 * (k : ℝ) := by
  induction k with
  | zero => simpa using And.intro hu (le_refl ‖inverseCoordinate u‖)
  | succ k ih =>
    have hkj : k ≤ J := Nat.le_trans (Nat.le_succ k) hk
    obtain ⟨hre, hnorm⟩ := ih hkj
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    have hJn : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
    have hkcast : (k : ℝ) ≤ (J : ℝ) := by exact_mod_cast hkj
    have hp : 64 ≤ (inverseCoordinate (orbit u s k)).re := by linarith
    have hlocal : ‖inverseCoordinate (orbit u s k)‖ ≤
        (‖inverseCoordinate u‖ + 2) * ((J : ℝ) + 1) := by
      nlinarith [mul_nonneg (norm_nonneg (inverseCoordinate u)) hJn]
    have hpar := local_parameter_bound ‖inverseCoordinate u‖
      (norm_nonneg _) J s (inverseCoordinate (orbit u s k)) hs hlocal
    have hsquarter := hs.trans (parameterRadius_le_quarter _ (norm_nonneg _) J)
    have hstep := inverse_step_bound s (orbit u s k) hp hsquarter hpar
    have hinc := coordinate_increment_bounds (inverseCoordinate (orbit u s k))
      (inverseCoordinate (unfolding s (orbit u s k))) hstep
    rw [← orbit_succ] at hinc
    constructor
    · have hh := hinc.1
      push_cast
      linarith
    · have hh := hinc.2
      push_cast
      linarith

/-- The actual finite perturbed orbit has the reciprocal decay needed for
Cauchy estimates, uniformly throughout the explicit parameter disc. -/
theorem finite_orbit_norm_bound (u s : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (J : ℕ)
    (hs : ‖s‖ ≤ parameterRadius ‖inverseCoordinate u‖ J)
    (k : ℕ) (hk : k ≤ J) :
    ‖orbit u s k‖ ≤ 2 / (R + (k : ℝ) / 2) := by
  have hre := (finite_orbit_inverse_bounds u s R hR hu J hs k hk).1
  have hden : 0 < R + (k : ℝ) / 2 := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact (norm_le_two_div_re _ (lt_of_lt_of_le hden hre)).trans
    (div_le_div_of_nonneg_left (by norm_num) hden hre)

/-- A common inverse-coordinate upper bound yields a common parameter disc,
as required when the initial point ranges over a compact petal subset. -/
theorem finite_orbit_norm_bound_of_upper_bound (u s : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (J : ℕ)
    (hs : ‖s‖ ≤ parameterRadius Z J) (k : ℕ) (hk : k ≤ J) :
    ‖orbit u s k‖ ≤ 2 / (R + (k : ℝ) / 2) := by
  exact finite_orbit_norm_bound u s R hR hu J
    (hs.trans (parameterRadius_antitone _ Z (norm_nonneg _) hZ J)) k hk

theorem finite_orbit_ne_zero (u s : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (J : ℕ)
    (hs : ‖s‖ ≤ parameterRadius ‖inverseCoordinate u‖ J)
    (k : ℕ) (hk : k ≤ J) : orbit u s k ≠ 0 := by
  have hre := (finite_orbit_inverse_bounds u s R hR hu J hs k hk).1
  have hp : 0 < R + (k : ℝ) / 2 := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  intro hz
  simp only [hz, inverseCoordinate, div_zero, Complex.zero_re] at hre
  linarith

/-- Every finite orbit of the actual exponential unfolding is entire in its
complex parameter. -/
theorem differentiable_orbit_parameter (u : ℂ) (k : ℕ) :
    Differentiable ℂ (fun s : ℂ => orbit u s k) := by
  induction k with
  | zero => simpa only [orbit_zero] using differentiable_const u
  | succ k ih =>
    have hd := ((differentiable_id.neg).add
      (((differentiable_const (1 : ℂ)).sub differentiable_id).mul ih)).cexp.sub_const (1 : ℂ)
    simpa [orbit_succ, unfolding] using hd

/-- Cauchy's estimate applied to the actual finite perturbed orbits gives the
linear parameter-velocity bound used by the first-order coefficient series.
Neither a Cauchy bound nor a velocity bound is assumed. -/
theorem orbitTangent_norm_bound (u : ℂ) (R : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (k : ℕ) :
    ‖orbitTangent u k‖ ≤ 384 * (‖inverseCoordinate u‖ + 2) ^ 2 * ((k : ℝ) + 1) := by
  have hr := parameterRadius_pos ‖inverseCoordinate u‖ (norm_nonneg _) k
  have hden : 0 < R + (k : ℝ) / 2 := by
    have hkn : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (f := fun s : ℂ => orbit u s k) (c := 0)
    (C := 2 / (R + (k : ℝ) / 2)) hr
    (differentiable_orbit_parameter u k).diffContOnCl
    (fun s hs => by
      have hn : ‖s‖ = parameterRadius ‖inverseCoordinate u‖ k := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hs
      exact finite_orbit_norm_bound u s R hR hu k hn.le k (le_refl k))
  rw [deriv_orbit_parameter_zero] at hcauchy
  apply hcauchy.trans
  apply (div_le_iff₀ hr).mpr
  have heq : (384 * (‖inverseCoordinate u‖ + 2) ^ 2 * ((k : ℝ) + 1)) *
      parameterRadius ‖inverseCoordinate u‖ k = 4 / ((k : ℝ) + 1) := by
    dsimp [parameterRadius]
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ hden (by positivity : 0 < (k : ℝ) + 1)).mpr
  linarith

/-- The linear velocity bound has a common constant on a petal subset with a
common inverse-coordinate upper bound. -/
theorem orbitTangent_norm_bound_of_upper_bound (u : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (k : ℕ) :
    ‖orbitTangent u k‖ ≤ 384 * (Z + 2) ^ 2 * ((k : ℝ) + 1) := by
  have hsq : (‖inverseCoordinate u‖ + 2) ^ 2 ≤ (Z + 2) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  exact (orbitTangent_norm_bound u R hR hu k).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) (by positivity))

/-- Cauchy's estimate of every order for the actual finite perturbed orbit,
uniform over initial coordinates with a common inverse-coordinate upper bound. -/
theorem orbit_parameter_higher_derivative_bound (u : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (j k : ℕ) :
    ‖iteratedDeriv j (fun s : ℂ => orbit u s k) 0‖ ≤
      (j.factorial : ℝ) * (2 / (R + (k : ℝ) / 2)) / (parameterRadius Z k) ^ j := by
  have hr := parameterRadius_pos Z ((norm_nonneg _).trans hZ) k
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le j hr
    (differentiable_orbit_parameter u k).diffContOnCl
    (fun s hs => by
      have hn : ‖s‖ = parameterRadius Z k := by
        simpa only [Metric.mem_sphere, dist_zero_right] using hs
      exact finite_orbit_norm_bound_of_upper_bound u s R Z hR hu hZ k hn.le k (le_refl k))

end Kneser.PerturbedExponentialOrbit
