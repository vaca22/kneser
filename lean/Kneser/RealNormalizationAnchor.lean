import Kneser.ParabolicCoordinateJacobian
import Kneser.ParabolicOverlapGate

/-!
The true real normalization anchor `exp (-1) - 1` enters every deep
parabolic petal.  The proof supplies a uniform reciprocal drift on the
entire real interval `[-1,0)`, rather than assuming basin membership.
-/

noncomputable section

namespace Kneser.RealNormalizationAnchor

open Filter Set Kneser.ParabolicExponentialOrbit
open Kneser.ParabolicCoordinateJacobian
open scoped Topology BigOperators

def realMap (x : ℝ) : ℝ := Real.exp x - 1

def realZeta (x : ℝ) : ℝ := -2 / x

def realAnchor : ℝ := Real.exp (-1) - 1

def normalizationAnchor : ℂ := (realAnchor : ℂ)

theorem normalizationAnchor_eq : normalizationAnchor = Complex.exp (-1) - 1 := by
  simp [normalizationAnchor, realAnchor, Complex.ofReal_exp]

/-- The actual Taylor remainder has the numerical coefficient `2/9`.
On the entire negative unit interval this gives a positive quadratic
increment, sufficient for reciprocal drift. -/
theorem realMap_increment (x : ℝ) (hx : -1 ≤ x) (hxneg : x < 0) :
    x ^ 2 / 4 ≤ realMap x - x := by
  have habs : |x| ≤ 1 := by rw [abs_of_neg hxneg]; linarith
  have hc : ‖(x : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using habs
  have h := Complex.exp_bound hc (n := 3) (by norm_num)
  have hs : (∑ m ∈ Finset.range 3, (x : ℂ) ^ m / (m.factorial : ℂ)) =
      1 + (x : ℂ) + (x : ℂ) ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at h
  have hre := (Complex.abs_re_le_norm (Complex.exp (x : ℂ) -
    (1 + (x : ℂ) + (x : ℂ) ^ 2 / 2))).trans h
  have hr : |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ |x| ^ 3 * (2 / 9) := by
    norm_num [Complex.exp_ofReal_re, Complex.norm_real, Real.norm_eq_abs, Nat.factorial,
      pow_two, Complex.mul_re] at hre ⊢
    exact hre
  rw [abs_of_neg hxneg] at hr
  have hl := (abs_le.mp hr).1
  have hp : 0 ≤ x ^ 2 * (1 + x) := mul_nonneg (sq_nonneg x) (by linarith)
  dsimp [realMap]
  nlinarith

theorem realMap_preserves_interval (x : ℝ) (hx : -1 ≤ x) (hxneg : x < 0) :
    -1 ≤ realMap x ∧ realMap x < 0 ∧ x ≤ realMap x := by
  have hi := realMap_increment x hx hxneg
  have hn : realMap x < 0 := by
    dsimp [realMap]
    linarith [(Real.exp_lt_one_iff).mpr hxneg]
  have hxle : x ≤ realMap x := by nlinarith [sq_nonneg x]
  exact ⟨hx.trans hxle, hn, hxle⟩

theorem realZeta_step (x : ℝ) (hx : -1 ≤ x) (hxneg : x < 0) :
    realZeta x + 1 / 2 ≤ realZeta (realMap x) := by
  obtain ⟨_, hyneg, hxle⟩ := realMap_preserves_interval x hx hxneg
  have hxy : 0 < x * realMap x := mul_pos_of_neg_of_neg hxneg hyneg
  have hxn : x ≠ 0 := ne_of_lt hxneg
  have hyn : realMap x ≠ 0 := ne_of_lt hyneg
  have he : realZeta (realMap x) - realZeta x =
      2 * (realMap x - x) / (x * realMap x) := by
    dsimp [realZeta]
    field_simp
    ring
  have hle : x * realMap x ≤ x ^ 2 := by
    have h := mul_le_mul_of_nonpos_left hxle hxneg.le
    nlinarith
  have hdiff : (1 / 2 : ℝ) ≤ realZeta (realMap x) - realZeta x := by
    rw [he]
    apply (le_div_iff₀ hxy).mpr
    nlinarith [realMap_increment x hx hxneg]
  linarith

theorem real_iterate_interval (x : ℝ) (hx : -1 ≤ x) (hxneg : x < 0) (n : ℕ) :
    -1 ≤ (realMap^[n]) x ∧ (realMap^[n]) x < 0 := by
  induction n with
  | zero => exact ⟨hx, hxneg⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨(realMap_preserves_interval _ ih.1 ih.2).1,
      (realMap_preserves_interval _ ih.1 ih.2).2.1⟩

theorem real_iterate_zeta_growth (x : ℝ) (hx : -1 ≤ x) (hxneg : x < 0) (n : ℕ) :
    realZeta x + (n : ℝ) / 2 ≤ realZeta ((realMap^[n]) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hn, hnneg⟩ := real_iterate_interval x hx hxneg n
    have hs := realZeta_step _ hn hnneg
    rw [Function.iterate_succ_apply']
    push_cast
    linarith

theorem parabolicMap_real (x : ℝ) : parabolicMap (x : ℂ) = (realMap x : ℂ) := by
  simp [parabolicMap, realMap, Complex.ofReal_exp]

theorem parabolic_iterate_real (x : ℝ) (n : ℕ) :
    (parabolicMap^[n]) (x : ℂ) = ((realMap^[n]) x : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, parabolicMap_real]

theorem inverseCoordinate_real_re (x : ℝ) : (inverseCoordinate (x : ℂ)).re = realZeta x := by
  simp [inverseCoordinate, realZeta]

theorem exists_real_orbit_enters_petal (x : ℝ) (hx : -1 ≤ x) (hxneg : x < 0) (R : ℝ) :
    ∃ N : ℕ, R < (inverseCoordinate ((parabolicMap^[N]) (x : ℂ))).re := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * (R - realZeta x))
  refine ⟨N, ?_⟩
  rw [parabolic_iterate_real, inverseCoordinate_real_re]
  linarith [real_iterate_zeta_growth x hx hxneg N]

theorem realAnchor_interval : -1 ≤ realAnchor ∧ realAnchor < 0 := by
  constructor
  · dsimp [realAnchor]
    linarith [Real.exp_pos (-1)]
  · dsimp [realAnchor]
    linarith [(Real.exp_lt_one_iff).mpr (by norm_num : (-1 : ℝ) < 0)]

/-- The actual base point in the manuscript reaches every specified
depth; its finite parameter orbit is jointly analytic at that point. -/
theorem exists_anchor_enters_petal (R : ℝ) :
    ∃ N : ℕ, R < (inverseCoordinate (ExponentialUnfolding.orbit normalizationAnchor 0 N)).re ∧
      AnalyticAt ℂ (fun p : ℂ × ℂ => ExponentialUnfolding.orbit p.2 p.1 N)
        (0, normalizationAnchor) := by
  obtain ⟨N, hN⟩ := exists_real_orbit_enters_petal realAnchor
    realAnchor_interval.1 realAnchor_interval.2 R
  refine ⟨N, ?_, ParabolicOverlapGate.analyticAt_forward_orbit_joint normalizationAnchor 0 N⟩
  simpa only [unfolding_orbit_zero_eq_iterate, normalizationAnchor] using hN

theorem exists_anchor_parameter_entry (R : ℝ) :
    ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧
      AnalyticAt ℂ (fun s => ExponentialUnfolding.orbit normalizationAnchor s N) 0 ∧
      ∀ s : ℂ, ‖s‖ < δ →
        R < (inverseCoordinate (ExponentialUnfolding.orbit normalizationAnchor s N)).re := by
  obtain ⟨N, hN, ha⟩ := exists_anchor_enters_petal (max R 1)
  have hparam : AnalyticAt ℂ (fun s => ExponentialUnfolding.orbit normalizationAnchor s N) 0 :=
    ha.comp (f := fun s : ℂ => (s, normalizationAnchor)) (analyticAt_id.prod analyticAt_const)
  have hpos : 0 < (inverseCoordinate (ExponentialUnfolding.orbit normalizationAnchor 0 N)).re :=
    lt_trans (by norm_num : (0 : ℝ) < 1) ((le_max_right R 1).trans_lt hN)
  have hne : ExponentialUnfolding.orbit normalizationAnchor 0 N ≠ 0 := by
    intro he
    simp [he, inverseCoordinate] at hpos
  have hc : ContinuousAt
      (fun s : ℂ => (inverseCoordinate (ExponentialUnfolding.orbit normalizationAnchor s N)).re) 0 :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.div hparam.continuousAt hne)
  have hevent := hc.eventually (lt_mem_nhds ((le_max_left R 1).trans_lt hN))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨N, δ, hδ, hparam, ?_⟩
  intro s hs
  exact hb (by simpa only [dist_zero_right] using hs)

def forwardSpatialJacobian (u : ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => Complex.exp ((parabolicMap^[k]) u) * forwardSpatialJacobian u k

theorem hasDerivAt_parabolic_iterate (u : ℂ) (n : ℕ) :
    HasDerivAt (parabolicMap^[n]) (forwardSpatialJacobian u n) u := by
  induction n with
  | zero => exact hasDerivAt_id u
  | succ n ih =>
    have hd := ((Complex.hasDerivAt_exp ((parabolicMap^[n]) u)).sub_const 1).comp u ih
    convert hd using 1 <;> first | rfl | (funext w; rw [Function.iterate_succ_apply']; rfl)

theorem forwardSpatialJacobian_ne_zero (u : ℂ) (n : ℕ) : forwardSpatialJacobian u n ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero
  | succ n ih => exact mul_ne_zero (Complex.exp_ne_zero _) ih

def transportedAttractingCoordinate (N : ℕ) (u : ℂ) : ℂ :=
  attractingCoordinate ((parabolicMap^[N]) u) - (N : ℂ)

def normalizedAttractingCoordinate (N : ℕ) (u : ℂ) : ℂ :=
  transportedAttractingCoordinate N u - transportedAttractingCoordinate N normalizationAnchor

theorem normalizedAttractingCoordinate_anchor (N : ℕ) :
    normalizedAttractingCoordinate N normalizationAnchor = 0 := by
  simp [normalizedAttractingCoordinate]

theorem transported_attracting_hasDerivAt (u : ℂ) (N : ℕ) (R : ℝ)
    (hc : CanonicalJacobian attractingCoordinate R)
    (hentry : R < (inverseCoordinate ((parabolicMap^[N]) u)).re) :
    AnalyticAt ℂ (transportedAttractingCoordinate N) u ∧
      HasDerivAt (transportedAttractingCoordinate N)
        (deriv attractingCoordinate ((parabolicMap^[N]) u) * forwardSpatialJacobian u N) u ∧
      deriv (transportedAttractingCoordinate N) u ≠ 0 := by
  obtain ⟨ha, hdn, _⟩ := hc.2 _ hentry
  have hia := (ParabolicFatouHolomorphic.differentiable_parabolicMap.iterate N).analyticAt u
  have hd := (ha.hasStrictDerivAt.hasDerivAt.comp u (hasDerivAt_parabolic_iterate u N)).sub_const (N : ℂ)
  change HasDerivAt (transportedAttractingCoordinate N)
    (deriv attractingCoordinate ((parabolicMap^[N]) u) * forwardSpatialJacobian u N) u at hd
  have hian : AnalyticAt ℂ (transportedAttractingCoordinate N) u :=
    (ha.comp (f := parabolicMap^[N]) hia).sub analyticAt_const
  refine ⟨hian, hd, ?_⟩
  rw [hd.deriv]
  exact mul_ne_zero hdn (forwardSpatialJacobian_ne_zero u N)

/-- The canonical Fatou coordinate extends to the actual real anchor by
a genuine finite forward orbit.  Subtracting its anchor value gives the
specified normalization, preserves the nonzero derivative and Abel
identity, and provides an analytic local inverse. -/
theorem exists_normalized_anchor_coordinate :
    ∃ N : ℕ, normalizedAttractingCoordinate N normalizationAnchor = 0 ∧
      AnalyticAt ℂ (normalizedAttractingCoordinate N) normalizationAnchor ∧
      deriv (normalizedAttractingCoordinate N) normalizationAnchor ≠ 0 ∧
      (∀ᶠ u in 𝓝 normalizationAnchor,
        normalizedAttractingCoordinate N (parabolicMap u) = normalizedAttractingCoordinate N u + 1) ∧
      ∃ I : ℂ → ℂ, AnalyticAt ℂ I 0 ∧ I 0 = normalizationAnchor ∧
        (∀ᶠ u in 𝓝 normalizationAnchor, I (normalizedAttractingCoordinate N u) = u) ∧
        (∀ᶠ w in 𝓝 0, normalizedAttractingCoordinate N (I w) = w) := by
  obtain ⟨Ra, hRa, hc, _⟩ := exists_attracting_canonicalJacobian
  obtain ⟨Rb, Cb, hRb, hCb, hab⟩ := ParabolicFatouCoordinate.exists_attracting_fatou_coordinate
  let R := max Ra Rb
  obtain ⟨N, hentry, _⟩ := exists_anchor_enters_petal R
  rw [unfolding_orbit_zero_eq_iterate] at hentry
  have hentera : Ra < (inverseCoordinate ((parabolicMap^[N]) normalizationAnchor)).re :=
    (le_max_left Ra Rb).trans_lt hentry
  obtain ⟨ha, hd, hdn⟩ := transported_attracting_hasDerivAt normalizationAnchor N Ra hc hentera
  have hna : AnalyticAt ℂ (normalizedAttractingCoordinate N) normalizationAnchor :=
    ha.sub analyticAt_const
  have hnd := hd.sub_const (transportedAttractingCoordinate N normalizationAnchor)
  have hnn : deriv (normalizedAttractingCoordinate N) normalizationAnchor ≠ 0 := by
    have he := hnd.deriv
    change deriv (normalizedAttractingCoordinate N) normalizationAnchor =
      deriv attractingCoordinate ((parabolicMap^[N]) normalizationAnchor) *
        forwardSpatialJacobian normalizationAnchor N at he
    rw [he]
    exact mul_ne_zero (hc.2 _ hentera).2.1 (forwardSpatialJacobian_ne_zero _ _)
  have hNcont : ContinuousAt (fun u : ℂ => (inverseCoordinate ((parabolicMap^[N]) u)).re)
      normalizationAnchor := by
    have hn : (parabolicMap^[N]) normalizationAnchor ≠ 0 := by
      intro he
      simp [he, inverseCoordinate] at hentera
      linarith
    exact Complex.continuous_re.continuousAt.comp
      (continuousAt_const.div (ParabolicFatouHolomorphic.differentiable_parabolicMap.iterate N).continuous.continuousAt hn)
  have hentrynear := hNcont.eventually (lt_mem_nhds ((le_max_right Ra Rb).trans_lt hentry))
  have hAbel : ∀ᶠ u in 𝓝 normalizationAnchor,
      normalizedAttractingCoordinate N (parabolicMap u) = normalizedAttractingCoordinate N u + 1 := by
    filter_upwards [hentrynear] with u hu
    have hi := (hab ((parabolicMap^[N]) u) hu.le).2.2.1
    have he : (parabolicMap^[N]) (parabolicMap u) = parabolicMap ((parabolicMap^[N]) u) := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
    dsimp [normalizedAttractingCoordinate, transportedAttractingCoordinate]
    rw [he]
    change attractingCoordinate (parabolicMap ((parabolicMap^[N]) u)) =
      attractingCoordinate ((parabolicMap^[N]) u) + 1 at hi
    rw [hi]
    ring
  obtain ⟨I, hIa, hI0, hleft, hright⟩ := exists_analytic_local_inverse
    (normalizedAttractingCoordinate N) normalizationAnchor hna hnn
  rw [normalizedAttractingCoordinate_anchor] at hIa hI0 hright
  exact ⟨N, normalizedAttractingCoordinate_anchor N, hna, hnn, hAbel, I, hIa, hI0, hleft, hright⟩

end Kneser.RealNormalizationAnchor

end
