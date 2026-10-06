import Kneser.ActualParameterHornCoefficient
import Kneser.ExponentialMultiplierSecondOrder
import Kneser.HeadTail
import Mathlib.Analysis.Analytic.Order

/-!
# Quantitative Fourier and horn-coefficient expansions

A uniform gate remainder is integrated by the actual Fourier operator.
Products and analytic composition preserve its order, including the
exponential normalization and the principal logarithm. The actual multiplier
parameter constructed from the exponential cusp converts the logarithmic
remainder from `s^q` to `‖p(s)‖^q`.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.QuantitativeHornExpansion

open Filter Set MeasureTheory Complex Kneser.GateFourierDerivative
open Kneser.ExponentialMultiplierParameter
open scoped Topology

/-- A quantitative first-order expansion on the positive real ray. -/
def PowerExpansion (f : ℝ → ℂ) (d : ℂ) (q : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
    ‖f s - f 0 - (s : ℂ) * d‖ ≤ C * s ^ q

theorem PowerExpansion.hasDerivWithinAt {f : ℝ → ℂ} {d : ℂ} {q : ℝ}
    (hf : PowerExpansion f d q) (hq : 1 < q) :
    HasDerivWithinAt f d (Ici 0) 0 := by
  obtain ⟨C, _, hC⟩ := hf
  exact Kneser.hasDerivWithinAt_of_power_error f d C q hq (by
    simpa only [Complex.real_smul] using hC)

theorem linear_increment_bound (f : ℝ → ℂ) (d : ℂ) (q C : ℝ)
    (hq : 1 ≤ q) (hC : 0 ≤ C)
    (hf : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - f 0 - (s : ℂ) * d‖ ≤ C * s ^ q) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s - f 0‖ ≤ (‖d‖ + C) * s := by
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hf, hpos, hle] with s hs hspos hs1
  have hp : s ^ q ≤ s := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hspos hs1 hq
  have heq : f s - f 0 = (f s - f 0 - (s : ℂ) * d) + (s : ℂ) * d := by ring
  rw [heq]
  calc
    _ ≤ ‖f s - f 0 - (s : ℂ) * d‖ + ‖(s : ℂ) * d‖ := norm_add_le _ _
    _ ≤ C * s ^ q + s * ‖d‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos]
      exact add_le_add hs le_rfl
    _ ≤ C * s + s * ‖d‖ := add_le_add (mul_le_mul_of_nonneg_left hp hC) le_rfl
    _ = _ := by ring

theorem PowerExpansion.const_mul {f : ℝ → ℂ} {d : ℂ} {q : ℝ}
    (hf : PowerExpansion f d q) (a : ℂ) : PowerExpansion (fun s => a * f s) (a * d) q := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨‖a‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hf] with s hs
  have heq : a * f s - a * f 0 - (s : ℂ) * (a * d) =
      a * (f s - f 0 - (s : ℂ) * d) := by ring
  rw [heq, norm_mul]
  exact (mul_le_mul_of_nonneg_left hs (norm_nonneg _)).trans_eq (by ring)

theorem PowerExpansion.sub {f g : ℝ → ℂ} {df dg : ℂ} {q : ℝ}
    (hf : PowerExpansion f df q) (hg : PowerExpansion g dg q) :
    PowerExpansion (fun s => f s - g s) (df - dg) q := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, add_nonneg hCf hCg, ?_⟩
  filter_upwards [hf, hg] with s hs ht
  have heq : (f s - g s) - (f 0 - g 0) - (s : ℂ) * (df - dg) =
      (f s - f 0 - (s : ℂ) * df) - (g s - g 0 - (s : ℂ) * dg) := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add hs ht).trans_eq (by ring))

theorem PowerExpansion.mul {f g : ℝ → ℂ} {df dg : ℂ} {q : ℝ}
    (hf : PowerExpansion f df q) (hg : PowerExpansion g dg q)
    (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    PowerExpansion (fun s => f s * g s) (df * g 0 + f 0 * dg) q := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  have hlinf := linear_increment_bound f df q Cf hq hCf hf
  have hling := linear_increment_bound g dg q Cg hq hCg hg
  let Kf := ‖df‖ + Cf
  let Kg := ‖dg‖ + Cg
  have hKf : 0 ≤ Kf := add_nonneg (norm_nonneg _) hCf
  have hKg : 0 ≤ Kg := add_nonneg (norm_nonneg _) hCg
  refine ⟨‖g 0‖ * Cf + ‖f 0‖ * Cg + Kf * Kg, by positivity, ?_⟩
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hf, hg, hlinf, hling, hpos, hle] with s hs ht hfs hgs hspos hs1
  have hp : s ^ (2 : ℕ) ≤ s ^ q := by
    have h := Real.rpow_le_rpow_of_exponent_ge hspos hs1 hq2
    norm_num [Real.rpow_natCast] at h
    exact h
  have heq : f s * g s - f 0 * g 0 - (s : ℂ) * (df * g 0 + f 0 * dg) =
      g 0 * (f s - f 0 - (s : ℂ) * df) +
      f 0 * (g s - g 0 - (s : ℂ) * dg) + (f s - f 0) * (g s - g 0) := by ring
  rw [heq]
  calc
    _ ≤ (‖g 0‖ * ‖f s - f 0 - (s : ℂ) * df‖ +
          ‖f 0‖ * ‖g s - g 0 - (s : ℂ) * dg‖) + ‖f s - f 0‖ * ‖g s - g 0‖ := by
      exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans_eq (by simp))
        (by rw [norm_mul]))
    _ ≤ (‖g 0‖ * (Cf * s ^ q) + ‖f 0‖ * (Cg * s ^ q)) + (Kf * s) * (Kg * s) := by
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
        (mul_le_mul_of_nonneg_left ht (norm_nonneg _)))
        (mul_le_mul hfs hgs (norm_nonneg _) (by positivity))
    _ ≤ (‖g 0‖ * Cf + ‖f 0‖ * Cg + Kf * Kg) * s ^ q := by
      have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg hKf hKg)
      nlinarith

/-- Analytic composition retains a `q`-order first-order remainder for
`1<q≤2`; its genuine Taylor remainder is constructed rather than assumed. -/
theorem PowerExpansion.comp_analytic {f : ℝ → ℂ} {df : ℂ} {q : ℝ}
    (hf : PowerExpansion f df q) (hq : 1 < q) (hq2 : q ≤ 2)
    (G : ℂ → ℂ) (hG : AnalyticAt ℂ G (f 0)) (dG : ℂ)
    (hGder : HasDerivAt G dG (f 0)) :
    PowerExpansion (fun s => G (f s)) (dG * df) q := by
  have hfder := hf.hasDerivWithinAt hq
  obtain ⟨Cf, hCf, hf⟩ := hf
  let H : ℂ → ℂ := fun z => G (f 0 + z)
  have hHa : AnalyticAt ℂ H 0 := hG.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  have hHder : HasDerivAt H dG 0 := by
    have hGder' : HasDerivAt G dG (f 0 + (0 : ℂ)) := by simpa using hGder
    convert hGder'.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add (f 0)) using 1
      <;> first | rfl | simp
  obtain ⟨R, hRa, hR⟩ := hHa.exists_eq_sum_add_pow_mul 2
  have hTaylor : ∀ z, H z = G (f 0) + z * dG + z ^ 2 * R z := by
    intro z
    have h := hR z
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
      iteratedDeriv_zero, iteratedDeriv_one, hHder.deriv] at h
    norm_num [H] at h
    simpa only [smul_eq_mul] using h
  have hlim : Tendsto (fun s => f s - f 0) (𝓝[>] 0) (𝓝 0) := by
    have ht := hfder.continuousWithinAt.tendsto.mono_left
      (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    simpa only [sub_self] using ht.sub_const (f 0)
  let KR := ‖R 0‖ + 1
  have hKR : 0 ≤ KR := by dsimp [KR]; positivity
  have hRb : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖R (f s - f 0)‖ ≤ KR :=
    ((hRa.continuousAt.tendsto.comp hlim).norm.eventually
      (gt_mem_nhds (by dsimp [KR]; linarith : ‖R 0‖ < KR))).mono fun _ h => h.le
  let Kf := ‖df‖ + Cf
  have hKf : 0 ≤ Kf := add_nonneg (norm_nonneg _) hCf
  have hlinf := linear_increment_bound f df q Cf hq.le hCf hf
  refine ⟨‖dG‖ * Cf + Kf ^ 2 * KR, by positivity, ?_⟩
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hf, hlinf, hRb, hpos, hle] with s hs hfs hRs hspos hs1
  have hp : s ^ (2 : ℕ) ≤ s ^ q := by
    have h := Real.rpow_le_rpow_of_exponent_ge hspos hs1 hq2
    norm_num [Real.rpow_natCast] at h
    exact h
  have heq : G (f s) - G (f 0) - (s : ℂ) * (dG * df) =
      dG * (f s - f 0 - (s : ℂ) * df) + (f s - f 0) ^ 2 * R (f s - f 0) := by
    have ht := hTaylor (f s - f 0)
    have he : H (f s - f 0) = G (f s) := by dsimp [H]; congr 1; ring
    rw [he] at ht
    rw [ht]
    ring
  rw [heq]
  calc
    _ ≤ ‖dG‖ * ‖f s - f 0 - (s : ℂ) * df‖ + ‖f s - f 0‖ ^ 2 * ‖R (f s - f 0)‖ := by
      convert norm_add_le (dG * (f s - f 0 - (s : ℂ) * df))
        ((f s - f 0) ^ 2 * R (f s - f 0)) using 1
      simp [norm_pow]
    _ ≤ ‖dG‖ * (Cf * s ^ q) + (Kf * s) ^ 2 * KR := by
      exact add_le_add (mul_le_mul_of_nonneg_left hs (norm_nonneg _))
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hfs 2) hRs (norm_nonneg _) (sq_nonneg _))
    _ ≤ (‖dG‖ * Cf + Kf ^ 2 * KR) * s ^ q := by
      have hm := mul_le_mul_of_nonneg_left hp (mul_nonneg (sq_nonneg Kf) hKR)
      nlinarith

/-- The actual Fourier interval integral preserves the gate's quantitative
remainder, with its explicit constant Fourier-weight norm. -/
theorem gateFourier_powerExpansion (n : ℤ) (Y q C : ℝ) (hC : 0 ≤ C)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (hInt : ∀ s, IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hD : IntervalIntegrable (fun x => D (gatePoint Y x) * gateWeight n Y x) volume 0 1)
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)‖ ≤ C * s ^ q) :
    PowerExpansion (fun s => gateFourierCoefficient n Y (T s)) (gateCorrectionCoefficient n Y D) q := by
  refine ⟨C * Real.exp (2 * Real.pi * (n : ℝ) * Y), by positivity, ?_⟩
  filter_upwards [hUniform] with s hs
  rw [coefficient_remainder_eq_integral n Y s T D (hInt s) (hInt 0) hD]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := (C * s ^ q) * Real.exp (2 * Real.pi * (n : ℝ) * Y))
    (f := fun x => (T s (gatePoint Y x) - T 0 (gatePoint Y x) -
      (s : ℂ) * D (gatePoint Y x)) * gateWeight n Y x) (by
        intro x hx
        rw [norm_mul, norm_gateWeight]
        exact mul_le_mul_of_nonneg_right (hs x (Ioc_subset_Icc_self
          (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx))) (Real.exp_pos _).le)
  convert h using 1
  simp
  ring

/-- The nonzero derivative `p'(0)=2` supplies the local comparison needed
to express a remainder in the actual multiplier parameter. -/
theorem parameter_norm_comparison (p : ℂ → ℂ) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ ‖p (s : ℂ)‖ := by
  have hp' : HasDerivAt p 2 ((0 : ℝ) : ℂ) := by simpa using hp
  have hd := hp'.comp_ofReal.hasDerivWithinAt (s := Ioi 0)
  have ht := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)).mp hd
  change Tendsto (fun s : ℝ => slope (fun x : ℝ => p (x : ℂ)) 0 s) (𝓝[>] 0) (𝓝 2) at ht
  have ht' : Tendsto (fun s : ℝ => p (s : ℂ) / (s : ℂ)) (𝓝[>] 0) (𝓝 2) := by
    simpa only [slope_def_module, sub_zero, Complex.ofReal_zero, hp0, Complex.real_smul,
      Complex.ofReal_inv, div_eq_mul_inv, mul_comm] using ht
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, 1 < ‖p (s : ℂ) / (s : ℂ)‖ :=
    ht'.norm.eventually (lt_mem_nhds (by norm_num : (1 : ℝ) < ‖(2 : ℂ)‖))
  filter_upwards [hb, self_mem_nhdsWithin] with s hs hspos
  have hspos' : 0 < s := hspos
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hspos'] at hs
  simpa only [one_mul] using ((lt_div_iff₀ hspos').mp hs).le

theorem identity_powerExpansion (q : ℝ) : PowerExpansion (fun s : ℝ => (s : ℂ)) 1 q := by
  refine ⟨0, le_refl _, Eventually.of_forall ?_⟩
  intro s
  simp

/-- The raw horn coefficient has the quantitative expansion for every integer
mode, including modes whose unperturbed coefficient vanishes. -/
theorem raw_horn_powerExpansion (n : ℤ) (tn t0 : ℝ → ℂ) (B a dtn dt0 : ℂ) (q : ℝ)
    (hq : 1 < q) (hq2 : q ≤ 2) (hn0 : tn 0 = B) (h00 : t0 0 = -a)
    (hn : PowerExpansion tn dtn q) (h0 : PowerExpansion t0 dt0 q) :
    PowerExpansion (Kneser.realHornCoefficient n tn t0)
      (Complex.exp (Kneser.fourierFrequency n * a) *
        (dtn - Kneser.fourierFrequency n * B * dt0)) q := by
  have harg := h0.const_mul (-Kneser.fourierFrequency n)
  have hexp := harg.comp_analytic hq hq2 Complex.exp (analyticAt_id.cexp)
    (Complex.exp (-Kneser.fourierFrequency n * t0 0)) (Complex.hasDerivAt_exp _)
  have hτ := hn.mul hexp hq.le hq2
  have heq : dtn * Complex.exp (-Kneser.fourierFrequency n * t0 0) +
      tn 0 * (Complex.exp (-Kneser.fourierFrequency n * t0 0) *
        (-Kneser.fourierFrequency n * dt0)) =
      Complex.exp (Kneser.fourierFrequency n * a) *
        (dtn - Kneser.fourierFrequency n * B * dt0) := by
    simp only [hn0, h00, mul_neg, neg_mul, neg_neg]
    ring
  rw [heq] at hτ
  exact hτ

/-- Quantitative exponential normalization and logarithm extraction for an
arbitrary Fourier mode, derived from the coefficient expansions themselves. -/
theorem horn_powerExpansions (n : ℤ) (tn t0 : ℝ → ℂ) (B a dtn dt0 : ℂ) (q : ℝ)
    (hq : 1 < q) (hq2 : q ≤ 2) (hn0 : tn 0 = B) (h00 : t0 0 = -a) (hB : B ≠ 0)
    (hn : PowerExpansion tn dtn q) (h0 : PowerExpansion t0 dt0 q) :
    PowerExpansion (Kneser.realHornCoefficient n tn t0)
      (Complex.exp (Kneser.fourierFrequency n * a) *
        (dtn - Kneser.fourierFrequency n * B * dt0)) q ∧
    PowerExpansion (fun s => Complex.log (Kneser.realNormalizedHornCoefficient n tn t0 s))
      (2 * Kneser.hornKappa n B dtn dt0) q := by
  have hτ' := raw_horn_powerExpansion n tn t0 B a dtn dt0 q hq hq2 hn0 h00 hn h0
  have hτ0 : Kneser.realHornCoefficient n tn t0 0 =
      B * Complex.exp (Kneser.fourierFrequency n * a) := by
    simp [Kneser.realHornCoefficient, hn0, h00]
  have hnorm := hτ'.const_mul ((Kneser.realHornCoefficient n tn t0 0)⁻¹)
  have hnorm' : PowerExpansion (Kneser.realNormalizedHornCoefficient n tn t0)
      (2 * Kneser.hornKappa n B dtn dt0) q := by
    convert hnorm using 1
    · funext s
      simp only [Kneser.realNormalizedHornCoefficient, div_eq_mul_inv, mul_comm]
    · rw [hτ0]
      dsimp [Kneser.hornKappa, Kneser.fourierFrequency]
      field_simp [hB, Complex.exp_ne_zero]
  have hbase := Kneser.realNormalizedHornCoefficient_zero n tn t0 B a hn0 h00 hB
  have hloga : AnalyticAt ℂ Complex.log (Kneser.realNormalizedHornCoefficient n tn t0 0) := by
    rw [hbase]
    exact analyticAt_clog Complex.one_mem_slitPlane
  have hlogder : HasDerivAt Complex.log 1 (Kneser.realNormalizedHornCoefficient n tn t0 0) := by
    rw [hbase]
    simpa using Complex.hasDerivAt_log (by simp : (1 : ℂ) ∈ Complex.slitPlane)
  exact ⟨hτ', by simpa only [one_mul] using hnorm'.comp_analytic hq hq2 Complex.log hloga 1 hlogder⟩

/-- The actual multiplier parameter converts the quantitative logarithm
expansion to the paper's `κ p + O(‖p‖^q)` statement. -/
theorem log_remainder_in_actual_parameter (f : ℝ → ℂ) (κ : ℂ) (q : ℝ)
    (hq : 1 < q) (hq2 : q ≤ 2) (hf0 : f 0 = 0) (hf : PowerExpansion f (2 * κ) q)
    (p : ℂ → ℂ) (hpa : AnalyticAt ℂ p 0) (hp0 : p 0 = 0) (hp : HasDerivAt p 2 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖f s - κ * p (s : ℂ)‖ ≤ C * ‖p (s : ℂ)‖ ^ q := by
  have hpe := (identity_powerExpansion q).comp_analytic hq hq2 p
    (by simpa using hpa) 2 (by simpa using hp)
  have hdiff := hf.sub (hpe.const_mul κ)
  obtain ⟨C, hC, hdiff⟩ := hdiff
  refine ⟨C, hC, ?_⟩
  filter_upwards [hdiff, parameter_norm_comparison p hp0 hp, self_mem_nhdsWithin] with s hs hcomp hspos
  simp only [hf0, Complex.ofReal_zero, hp0, mul_zero, sub_self, sub_zero, mul_one] at hs
  rw [show (2 : ℂ) * κ - κ * 2 = 0 by ring, mul_zero, sub_zero] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by exact (show 0 < s from hspos).le) hcomp (by linarith)) hC)

/-- Quantitative Theorem D coefficient algebra for the actual Fourier
integrals and the constructed multiplier parameter. The only analytic
transition-map input is its uniform gate remainder. -/
theorem exists_actual_quantitative_horn_expansion (n : ℤ) (Y q Cgate : ℝ)
    (hq : 1 < q) (hq2 : q ≤ 2) (hCgate : 0 ≤ Cgate)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (B a : ℂ)
    (hInt : ∀ m s, IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hD : ∀ m, IntervalIntegrable (fun x => D (gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)‖ ≤
        Cgate * s ^ q)
    (hn0 : gateFourierCoefficient n Y (T 0) = B)
    (h00 : gateFourierCoefficient 0 Y (T 0) = -a) (hB : B ≠ 0) :
    let tn := fun s => gateFourierCoefficient n Y (T s)
    let t0 := fun s => gateFourierCoefficient 0 Y (T s)
    let δn := gateCorrectionCoefficient n Y D
    let δ0 := gateCorrectionCoefficient 0 Y D
    let κ := Kneser.hornKappa n B δn δ0
    ∃ V p : ℂ → ℂ, ∃ Cτ Cp : ℝ,
      AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧
      (∀ᶠ x in 𝓝 0, Kneser.ExponentialCuspParameter.cuspParameter (V x) = x ^ 2) ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      (∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) ∧
      0 ≤ Cτ ∧ 0 ≤ Cp ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖tn s - B - (s : ℂ) * δn‖ ≤
          (Cgate * Real.exp (2 * Real.pi * (n : ℝ) * Y)) * s ^ q) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖Kneser.realHornCoefficient n tn t0 s -
          B * Complex.exp (Kneser.fourierFrequency n * a) -
          (s : ℂ) * (Complex.exp (Kneser.fourierFrequency n * a) *
            (δn - Kneser.fourierFrequency n * B * δ0))‖ ≤ Cτ * s ^ q) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖Complex.log (Kneser.realNormalizedHornCoefficient n tn t0 s) - κ * p (s : ℂ)‖ ≤
          Cp * ‖p (s : ℂ)‖ ^ q) := by
  dsimp only
  have hn := gateFourier_powerExpansion n Y q Cgate hCgate T D (hInt n) (hD n) hUniform
  have h0 := gateFourier_powerExpansion 0 Y q Cgate hCgate T D (hInt 0) (hD 0) hUniform
  have hh := horn_powerExpansions n _ _ B a _ _ q hq hq2 hn0 h00 hB hn h0
  obtain ⟨Cτ, hCτ, hτbound⟩ := hh.1
  obtain ⟨V, p, hVa, hV0, hVsquare, hpa, hp0, hpder, hproduct⟩ :=
    exists_analytic_multiplier_parameter
  obtain ⟨Cp, hCp, hplog⟩ := log_remainder_in_actual_parameter _ _ q hq hq2
    (Kneser.log_realNormalizedHornCoefficient_zero n _ _ B a hn0 h00 hB) hh.2 p hpa hp0 hpder
  refine ⟨V, p, Cτ, Cp, hVa, hV0, hVsquare, hpa, hp0, hpder, hproduct, hCτ, hCp, ?_, ?_, hplog⟩
  · -- The explicit Fourier constant follows from the same integral estimate.
    filter_upwards [hUniform] with s hs
    rw [← hn0, coefficient_remainder_eq_integral n Y s T D (hInt n s) (hInt n 0) (hD n)]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1)
      (C := (Cgate * s ^ q) * Real.exp (2 * Real.pi * (n : ℝ) * Y))
      (f := fun x => (T s (gatePoint Y x) - T 0 (gatePoint Y x) -
        (s : ℂ) * D (gatePoint Y x)) * gateWeight n Y x) (by
          intro x hx
          rw [norm_mul, norm_gateWeight]
          exact mul_le_mul_of_nonneg_right (hs x (Ioc_subset_Icc_self
            (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx))) (Real.exp_pos _).le)
    convert h using 1
    simp
    ring
  · rw [Kneser.realHornCoefficient_zero n
      (fun s => gateFourierCoefficient n Y (T s))
      (fun s => gateFourierCoefficient 0 Y (T s)) B a hn0 h00] at hτbound
    exact hτbound

/-- The quantitative horn expansion and `p(s)=2s+(10/9)s²+O(‖s‖³)`
hold for the same constructed multiplier parameter. In particular, the
second-order parameter assertion does not select an independent witness. -/
theorem exists_actual_quantitative_horn_expansion_second_order (n : ℤ) (Y q Cgate : ℝ)
    (hq : 1 < q) (hq2 : q ≤ 2) (hCgate : 0 ≤ Cgate)
    (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (B a : ℂ)
    (hInt : ∀ m s, IntervalIntegrable
      (fun x => (T s (gatePoint Y x) - gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hD : ∀ m, IntervalIntegrable (fun x => D (gatePoint Y x) * gateWeight m Y x) volume 0 1)
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖T s (gatePoint Y x) - T 0 (gatePoint Y x) - (s : ℂ) * D (gatePoint Y x)‖ ≤
        Cgate * s ^ q)
    (hn0 : gateFourierCoefficient n Y (T 0) = B)
    (h00 : gateFourierCoefficient 0 Y (T 0) = -a) (hB : B ≠ 0) :
    let tn := fun s => gateFourierCoefficient n Y (T s)
    let t0 := fun s => gateFourierCoefficient 0 Y (T s)
    let δn := gateCorrectionCoefficient n Y D
    let δ0 := gateCorrectionCoefficient 0 Y D
    let κ := Kneser.hornKappa n B δn δ0
    ∃ V p R : ℂ → ℂ, ∃ Cτ Cp C2 : ℝ,
      AnalyticAt ℂ V 0 ∧ V 0 = 0 ∧
      (∀ᶠ x in 𝓝 0, Kneser.ExponentialCuspParameter.cuspParameter (V x) = x ^ 2) ∧
      AnalyticAt ℂ p 0 ∧ p 0 = 0 ∧ HasDerivAt p 2 0 ∧
      (∀ x, p (x ^ 2) = -Complex.log (1 + V x) * Complex.log (1 + V (-x))) ∧
      AnalyticAt ℂ R 0 ∧
      (∀ s, p s = 2 * s + (10 / 9) * s ^ 2 + s ^ 3 * R s) ∧
      0 ≤ Cτ ∧ 0 ≤ Cp ∧ 0 ≤ C2 ∧
      (∀ᶠ s : ℂ in 𝓝 0,
        ‖p s - 2 * s - (10 / 9) * s ^ 2‖ ≤ C2 * ‖s‖ ^ 3) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖tn s - B - (s : ℂ) * δn‖ ≤
          (Cgate * Real.exp (2 * Real.pi * (n : ℝ) * Y)) * s ^ q) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖Kneser.realHornCoefficient n tn t0 s -
          B * Complex.exp (Kneser.fourierFrequency n * a) -
          (s : ℂ) * (Complex.exp (Kneser.fourierFrequency n * a) *
            (δn - Kneser.fourierFrequency n * B * δ0))‖ ≤ Cτ * s ^ q) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        ‖Complex.log (Kneser.realNormalizedHornCoefficient n tn t0 s) - κ * p (s : ℂ)‖ ≤
          Cp * ‖p (s : ℂ)‖ ^ q) := by
  dsimp only
  obtain ⟨V, p, Cτ, Cp, hVa, hV0, hSquare, hpa, hp0, hpder, hproduct,
      hCτ, hCp, htn, hτ, hlog⟩ :=
    exists_actual_quantitative_horn_expansion n Y q Cgate hq hq2 hCgate
      T D B a hInt hD hUniform hn0 h00 hB
  obtain ⟨R, hRa, hR⟩ := Kneser.ExponentialMultiplierSecondOrder.multiplier_second_order
    V p hVa hV0 hSquare hpa hp0 hpder hproduct
  obtain ⟨C2, hC2, hC2bound⟩ :=
    Kneser.ExponentialMultiplierSecondOrder.second_order_remainder_bound p R hRa hR
  exact ⟨V, p, R, Cτ, Cp, C2, hVa, hV0, hSquare, hpa, hp0, hpder, hproduct,
    hRa, hR, hCτ, hCp, hC2, hC2bound, htn, hτ, hlog⟩

end Kneser.QuantitativeHornExpansion

end
