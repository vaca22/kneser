import Kneser.StableHolomorphicInverse
import Kneser.QuantitativeHornExpansion
import Kneser.GateInverseDerivative
import Kneser.CauchyHeadTaylor

/-!
# Quantitative moving gates

The moving branch is constructed on a common image disc. Uniform coordinate
expansions are then transported by genuine spatial Taylor estimates. Analytic
finite orbit curves may also be substituted into the same expansions.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.QuantitativeGateTransition

open Filter Set Metric Kneser.QuantitativeHornExpansion
open scoped Topology

/-- A genuine Cauchy estimate uniformly controls spatial Taylor remainders
at every point of the inner closed disc. -/
theorem norm_spatial_first_remainder_le (f : ℂ → ℂ) (r M : ℝ)
    (hr : 0 < r) (hM : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (ball (0 : ℂ) (4 * r)))
    (hbound : ∀ w ∈ closedBall (0 : ℂ) (4 * r), ‖f w‖ ≤ M)
    (u δ : ℂ) (hu : u ∈ closedBall (0 : ℂ) r) (hδ : ‖δ‖ ≤ r / 2) :
    ‖f (u + δ) - f u - deriv f u * δ‖ ≤ (2 * M / r ^ 2) * ‖δ‖ ^ 2 := by
  have hun : ‖u‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hu
  let g : ℂ → ℂ := fun w => f (u + w)
  have hg : DiffContOnCl ℂ g (ball (0 : ℂ) r) := by
    apply hf.comp ((differentiable_const u).add differentiable_id).diffContOnCl
    intro w hw
    have hwn : ‖w‖ < r := by simpa [mem_ball, dist_zero_right] using hw
    have h := norm_add_le u w
    simp only [Pi.add_apply, id_eq, mem_ball, dist_zero_right]
    linarith
  have hgb : ∀ w ∈ sphere (0 : ℂ) r, ‖g w‖ ≤ M := by
    intro w hw
    apply hbound (u + w)
    have hwn : ‖w‖ = r := by simpa [mem_sphere, dist_zero_right] using hw
    have h := norm_add_le u w
    simp only [mem_closedBall, dist_zero_right]
    linarith
  have hdu := hf.differentiableAt isOpen_ball (show u ∈ ball (0 : ℂ) (4 * r) by
    simp only [mem_ball, dist_zero_right]; linarith)
  have hdg : HasDerivAt g (deriv f u) 0 := by
    have hd : HasDerivAt f (deriv f u) (u + (0 : ℂ)) := by simpa using hdu.hasDerivAt
    simpa [g, Function.comp_def] using hd.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add u)
  have h := Kneser.CauchyHeadTaylor.norm_first_remainder_le g r M δ hr hM hg hgb hδ
  convert h using 1
  · simp [g, hdg.deriv, mul_comm]
  · ring

/-- Cauchy's derivative estimate and the mean-value inequality give a
uniform spatial Lipschitz bound directly from disc holomorphy and a norm bound. -/
theorem norm_sub_le_spatial_lipschitz (f : ℂ → ℂ) (r M : ℝ) (hr : 0 < r)
    (hf : DiffContOnCl ℂ f (ball (0 : ℂ) (4 * r)))
    (hbound : ∀ w ∈ closedBall (0 : ℂ) (4 * r), ‖f w‖ ≤ M)
    (u v : ℂ) (hu : u ∈ closedBall (0 : ℂ) r) (hv : v ∈ closedBall (0 : ℂ) r) :
    ‖f u - f v‖ ≤ (M / r) * ‖u - v‖ := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) (2 * r) := by
    intro x hx
    have hn : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hx
    simp only [mem_ball, dist_zero_right]
    linarith
  apply Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
    (s := closedBall (0 : ℂ) r)
    (fun x hx => hf.differentiableAt isOpen_ball (by
      have hn : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hx
      simp only [mem_ball, dist_zero_right]; linarith))
    (fun x hx => Kneser.StableHolomorphicInverse.norm_deriv_le_of_disc_bound f r M hr hf hbound
      x (hsub hx)) (convex_closedBall (0 : ℂ) r) hv hu

/-- Restricting a genuinely analytic complex curve to the positive real ray
has the required quantitative first-order expansion. -/
theorem analytic_curve_powerExpansion (w : ℂ → ℂ) (q : ℝ)
    (hw : AnalyticAt ℂ w 0) (hq : 1 < q) (hq2 : q ≤ 2) :
    PowerExpansion (fun s : ℝ => w (s : ℂ)) (deriv w 0) q := by
  have hid : PowerExpansion (fun s : ℝ => (s : ℂ)) 1 q := by
    refine ⟨0, le_rfl, Eventually.of_forall ?_⟩
    intro s
    simp
  simpa only [mul_one] using hid.comp_analytic hq hq2 w hw (deriv w 0) hw.differentiableAt.hasDerivAt

/-- A uniform family expansion can be evaluated along a quantitative moving
curve. Both fixed-map Taylor estimates come from spatial analyticity; no
moving-composition remainder is an input. -/
theorem moving_evaluation_powerExpansion (A : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (K : Set ℂ) (w : ℝ → ℂ) (dw : ℂ) (q C : ℝ)
    (hq : 1 < q) (hq2 : q ≤ 2) (hC : 0 ≤ C)
    (hw : PowerExpansion w dw q)
    (hA0 : AnalyticAt ℂ (A 0) (w 0)) (hD : AnalyticAt ℂ D (w 0))
    (hwK : ∀ᶠ s : ℝ in 𝓝[>] 0, w s ∈ K)
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
      ‖A s u - A 0 u - (s : ℂ) * D u‖ ≤ C * s ^ q) :
    PowerExpansion (fun s => A s (w s))
      (D (w 0) + deriv (A 0) (w 0) * dw) q := by
  have hfixed := hw.comp_analytic hq hq2 (A 0) hA0 (deriv (A 0) (w 0)) hA0.differentiableAt.hasDerivAt
  have hDc := hw.comp_analytic hq hq2 D hD (deriv D (w 0)) hD.differentiableAt.hasDerivAt
  obtain ⟨CA, hCA, hfixed⟩ := hfixed
  obtain ⟨CD, hCD, hDc⟩ := hDc
  let KD := ‖deriv D (w 0) * dw‖ + CD
  have hKD : 0 ≤ KD := add_nonneg (norm_nonneg _) hCD
  have hDlin := linear_increment_bound (fun s => D (w s))
    (deriv D (w 0) * dw) q CD hq.le hCD hDc
  refine ⟨C + CA + KD, by positivity, ?_⟩
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hUniform, hwK, hfixed, hDlin, hpos, hle] with s hs hws hfs hDs hsp hs1
  have hp : s ^ (2 : ℕ) ≤ s ^ q := by
    simpa [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hsp hs1 hq2
  have heq : A s (w s) - A 0 (w 0) -
      (s : ℂ) * (D (w 0) + deriv (A 0) (w 0) * dw) =
      (A s (w s) - A 0 (w s) - (s : ℂ) * D (w s)) +
      (A 0 (w s) - A 0 (w 0) - (s : ℂ) * (deriv (A 0) (w 0) * dw)) +
      (s : ℂ) * (D (w s) - D (w 0)) := by ring
  rw [heq]
  calc
    _ ≤ (‖A s (w s) - A 0 (w s) - (s : ℂ) * D (w s)‖ +
        ‖A 0 (w s) - A 0 (w 0) - (s : ℂ) * (deriv (A 0) (w 0) * dw)‖) +
        ‖(s : ℂ) * (D (w s) - D (w 0))‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (C * s ^ q + CA * s ^ q) + s * (KD * s) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
      exact add_le_add (add_le_add (hs _ hws) hfs)
        (mul_le_mul_of_nonneg_left hDs hsp.le)
    _ ≤ (C + CA + KD) * s ^ q := by
      have h := mul_le_mul_of_nonneg_left hp hKD
      nlinarith

/-- Finite analytic orbit transport, with a quantified remainder inherited
from the uniform coordinate expansion. -/
theorem analytic_moving_evaluation_powerExpansion (A : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (K : Set ℂ) (w : ℂ → ℂ) (q C : ℝ)
    (hq : 1 < q) (hq2 : q ≤ 2) (hC : 0 ≤ C)
    (hw : AnalyticAt ℂ w 0)
    (hA0 : AnalyticAt ℂ (A 0) (w 0)) (hD : AnalyticAt ℂ D (w 0))
    (hwK : ∀ᶠ s : ℝ in 𝓝[>] 0, w (s : ℂ) ∈ K)
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
      ‖A s u - A 0 u - (s : ℂ) * D u‖ ≤ C * s ^ q) :
    PowerExpansion (fun s : ℝ => A s (w (s : ℂ)))
      (D (w 0) + deriv (A 0) (w 0) * deriv w 0) q := by
  exact moving_evaluation_powerExpansion A D K (fun s => w (s : ℂ)) (deriv w 0) q C
    hq hq2 hC (analytic_curve_powerExpansion w q hw hq hq2) hA0 hD hwK hUniform

/-- The inverse remainder follows algebraically from the inverse equation
and the spatial estimates derived above by Cauchy's formula. -/
theorem norm_inverse_power_remainder (s q C K L M N : ℝ)
    (Ssv S0v S0v0 B Dv D0 v v0 : ℂ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hq2 : q ≤ 2)
    (_hC : 0 ≤ C) (hK : 0 ≤ K) (hL : 0 ≤ L) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hB : B ≠ 0) (hBinv : ‖B‖⁻¹ ≤ N) (hInv : Ssv = S0v0)
    (hParam : ‖Ssv - S0v - (s : ℂ) * Dv‖ ≤ C * s ^ q)
    (hSpatial : ‖S0v - S0v0 - B * (v - v0)‖ ≤ K * ‖v - v0‖ ^ 2)
    (hD : ‖Dv - D0‖ ≤ L * ‖v - v0‖) (hmove : ‖v - v0‖ ≤ M * s) :
    ‖v - v0 + (s : ℂ) * (D0 / B)‖ ≤ N * (C + K * M ^ 2 + L * M) * s ^ q := by
  have hp : s ^ (2 : ℕ) ≤ s ^ q := by
    simpa [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hs hs1 hq2
  have heq : v - v0 + (s : ℂ) * (D0 / B) = B⁻¹ *
      (-(Ssv - S0v - (s : ℂ) * Dv) -
        (S0v - S0v0 - B * (v - v0)) + (s : ℂ) * (D0 - Dv)) := by
    rw [hInv]
    field_simp
    ring
  have hsp : ‖S0v - S0v0 - B * (v - v0)‖ ≤ K * M ^ 2 * s ^ 2 := by
    exact hSpatial.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hmove 2) hK).trans_eq (by ring))
  have hd : ‖(s : ℂ) * (D0 - Dv)‖ ≤ L * M * s ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, norm_sub_rev]
    exact (mul_le_mul_of_nonneg_left (hD.trans
      (mul_le_mul_of_nonneg_left hmove hL)) hs.le).trans_eq (by ring)
  have hn : ‖-(Ssv - S0v - (s : ℂ) * Dv) -
      (S0v - S0v0 - B * (v - v0)) + (s : ℂ) * (D0 - Dv)‖ ≤
      (C + K * M ^ 2 + L * M) * s ^ q := by
    calc
      _ ≤ (‖Ssv - S0v - (s : ℂ) * Dv‖ +
          ‖S0v - S0v0 - B * (v - v0)‖) + ‖(s : ℂ) * (D0 - Dv)‖ := by
        exact (norm_add_le _ _).trans
          (add_le_add ((norm_sub_le _ _).trans_eq (by rw [norm_neg])) le_rfl)
      _ ≤ C * s ^ q + K * M ^ 2 * s ^ 2 + L * M * s ^ 2 := add_le_add (add_le_add hParam hsp) hd
      _ ≤ (C + K * M ^ 2 + L * M) * s ^ q := by
        have h1 := mul_le_mul_of_nonneg_left hp (mul_nonneg hK (sq_nonneg M))
        have h2 := mul_le_mul_of_nonneg_left hp (mul_nonneg hL hM)
        nlinarith
  rw [heq, norm_mul, norm_inv]
  exact (mul_le_mul hBinv hn (norm_nonneg _) hN).trans_eq (by ring)

/-- A quantitative moving inverse is constructed from uniform coordinate
expansions and spatial holomorphy. The common inverse, its analyticity, and
its uniform first-order expansion are all outputs. -/
theorem exists_quantitative_inverse_family (F : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (r q C MF MD : ℝ) (hr : 0 < r) (hq : 1 < q) (hq2 : q ≤ 2)
    (hC : 0 ≤ C) (hMF : 0 ≤ MF) (hMD : 0 ≤ MD) (h00 : F 0 0 = 0)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4))
    (ha0 : DiffContOnCl ℂ (F 0) (ball (0 : ℂ) (4 * r)))
    (ha : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (F s) (ball (0 : ℂ) (4 * r)))
    (hDa : DiffContOnCl ℂ D (ball (0 : ℂ) (4 * r)))
    (hFbound : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖F 0 x‖ ≤ MF)
    (hDbound : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖D x‖ ≤ MD)
    (hUniform : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s x - F 0 x - (s : ℂ) * D x‖ ≤ C * s ^ q) :
    ∃ V : ℝ → ℂ → ℂ, ∃ CV ≥ 0,
      (∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z) ∧
      AnalyticOnNhd ℂ (V 0) (ball (0 : ℂ) (r / 4)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ z ∈ ball (0 : ℂ) (r / 4), V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z) ∧
        AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) (r / 4)) ∧
        (∀ z ∈ ball (0 : ℂ) (r / 4),
          ‖V s z - V 0 z + (s : ℂ) * (D (V 0 z) / deriv (F 0) (V 0 z))‖ ≤ CV * s ^ q)) := by
  let K := MD + C
  let M := 2 * K
  let KT := 2 * MF / r ^ 2
  let LD := MD / r
  have hK : 0 ≤ K := add_nonneg hMD hC
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hKT : 0 ≤ KT := by dsimp [KT]; positivity
  have hLD : 0 ≤ LD := by dsimp [LD]; positivity
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  have hlin : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s x - F 0 x‖ ≤ K * s := by
    filter_upwards [hUniform, hpos, hle] with s hs hsp hs1
    intro x hx
    have hp : s ^ q ≤ s := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hsp hs1 hq.le
    have heq : F s x - F 0 x = (F s x - F 0 x - (s : ℂ) * D x) + (s : ℂ) * D x := by ring
    rw [heq]
    calc
      _ ≤ ‖F s x - F 0 x - (s : ℂ) * D x‖ + ‖(s : ℂ) * D x‖ := norm_add_le _ _
      _ ≤ C * s ^ q + s * MD := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
        exact add_le_add (hs x hx) (mul_le_mul_of_nonneg_left (hDbound x hx) hsp.le)
      _ ≤ K * s := by dsimp [K]; nlinarith [mul_le_mul_of_nonneg_left hp hC]
  have hKlim : Tendsto (fun s : ℝ => K * s) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).const_mul K).mono_left nhdsWithin_le_nhds
  obtain ⟨V, hV0, hVa0, hV, _⟩ := Kneser.StableHolomorphicInverse.exists_stable_inverse_family
    F r (fun s => K * s) hr h00 hF0 ha0 ha hKlim hlin
  have hhalf : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    intro x hx y hy
    exact (hF0 x hx y hy).trans (by norm_num; nlinarith [norm_nonneg (x-y)])
  have hFa0 : AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) (2 * r)) := by
    intro x hx
    exact ha0.differentiableOn.analyticAt (isOpen_ball.mem_nhds (by
      simp only [mem_ball, dist_zero_right] at hx ⊢; linarith))
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, M * s ≤ r / 2 := by
    have hm : Tendsto (fun s : ℝ => M * s) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).const_mul M).mono_left nhdsWithin_le_nhds
    exact (hm.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 2))).mono fun _ h => h.le
  refine ⟨V, 2 * (C + KT * M ^ 2 + LD * M), by positivity, hV0, hVa0, ?_⟩
  filter_upwards [hV, hUniform, hpos, hle, hsmall] with s hs hu hsp hs1 hsmall
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro z hz
  have hv := hs.1 z hz
  have hv0 := hV0 z hz
  have hmove : ‖V s z - V 0 z‖ ≤ M * s := by
    simpa [M, mul_assoc] using hs.2.2 z hz
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) (2 * r) := by
    intro x hx
    have hn : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hx
    simp only [mem_ball, dist_zero_right]; linarith
  have hBnorm := Kneser.StableHolomorphicInverse.norm_deriv_lower (F 0) r hhalf hFa0
    (V 0 z) (hsub hv0.1)
  have hB : deriv (F 0) (V 0 z) ≠ 0 := by intro h; rw [h, norm_zero] at hBnorm; linarith
  have hBinv : ‖deriv (F 0) (V 0 z)‖⁻¹ ≤ (2 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hBnorm
  apply norm_inverse_power_remainder s q C KT LD M 2
    (F s (V s z)) (F 0 (V s z)) (F 0 (V 0 z)) (deriv (F 0) (V 0 z))
    (D (V s z)) (D (V 0 z)) (V s z) (V 0 z)
    hsp hs1 hq2 hC hKT hLD hM (by norm_num) hB hBinv (hv.2.trans hv0.2.symm)
  · exact hu _ (by
      have hn : ‖V s z‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hv.1
      simp only [mem_closedBall, dist_zero_right]; linarith)
  · convert norm_spatial_first_remainder_le (F 0) r MF hr hMF ha0 hFbound
      (V 0 z) (V s z - V 0 z) hv0.1 (hmove.trans hsmall) using 1
    simp
  · exact norm_sub_le_spatial_lipschitz D r MD hr hDa hDbound (V s z) (V 0 z) hv.1 hv0.1
  · exact hmove

/-- Quantitative composition algebra, with spatial estimates furnished by
Cauchy's formula and a constructed quantitative inverse. -/
theorem norm_normalized_composition_power_remainder
    (s q CA KT LD M MA CV CStar : ℝ)
    (Asv A0v A0v0 DAv DA0 Asp v v0 dv AStarS AStar0 DAStar : ℂ)
    (hs : 0 < s) (hs1 : s ≤ 1) (hq2 : q ≤ 2)
    (hKT : 0 ≤ KT) (hLD : 0 ≤ LD) (hM : 0 ≤ M) (hMA : 0 ≤ MA)
    (hAsp : ‖Asp‖ ≤ MA)
    (hA : ‖Asv - A0v - (s : ℂ) * DAv‖ ≤ CA * s ^ q)
    (hSpatial : ‖A0v - A0v0 - Asp * (v - v0)‖ ≤ KT * ‖v - v0‖ ^ 2)
    (hDA : ‖DAv - DA0‖ ≤ LD * ‖v - v0‖)
    (hMove : ‖v - v0‖ ≤ M * s)
    (hV : ‖v - v0 - (s : ℂ) * dv‖ ≤ CV * s ^ q)
    (hStar : ‖AStarS - AStar0 - (s : ℂ) * DAStar‖ ≤ CStar * s ^ q) :
    ‖(Asv - AStarS) - (A0v0 - AStar0) -
      (s : ℂ) * (DA0 + Asp * dv - DAStar)‖ ≤
      (CA + KT * M ^ 2 + LD * M + MA * CV + CStar) * s ^ q := by
  have hp : s ^ (2 : ℕ) ≤ s ^ q := by
    simpa [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hs hs1 hq2
  have heq : (Asv - AStarS) - (A0v0 - AStar0) -
      (s : ℂ) * (DA0 + Asp * dv - DAStar) =
      (Asv - A0v - (s : ℂ) * DAv) +
        (A0v - A0v0 - Asp * (v - v0)) + (s : ℂ) * (DAv - DA0) +
        Asp * (v - v0 - (s : ℂ) * dv) - (AStarS - AStar0 - (s : ℂ) * DAStar) := by ring
  have hsp : ‖A0v - A0v0 - Asp * (v - v0)‖ ≤ KT * M ^ 2 * s ^ 2 :=
    hSpatial.trans ((mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hMove 2) hKT).trans_eq (by ring))
  have hd : ‖(s : ℂ) * (DAv - DA0)‖ ≤ LD * M * s ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    exact (mul_le_mul_of_nonneg_left (hDA.trans
      (mul_le_mul_of_nonneg_left hMove hLD)) hs.le).trans_eq (by ring)
  have hv : ‖Asp * (v - v0 - (s : ℂ) * dv)‖ ≤ MA * CV * s ^ q := by
    rw [norm_mul]
    exact (mul_le_mul hAsp hV (norm_nonneg _) hMA).trans_eq (by ring)
  rw [heq]
  calc
    _ ≤ (((‖Asv - A0v - (s : ℂ) * DAv‖ +
        ‖A0v - A0v0 - Asp * (v - v0)‖) + ‖(s : ℂ) * (DAv - DA0)‖) +
        ‖Asp * (v - v0 - (s : ℂ) * dv)‖) + ‖AStarS - AStar0 - (s : ℂ) * DAStar‖ := by
      exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans
        (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
    _ ≤ CA * s ^ q + KT * M ^ 2 * s ^ 2 + LD * M * s ^ 2 + MA * CV * s ^ q + CStar * s ^ q :=
      add_le_add (add_le_add (add_le_add (add_le_add hA hsp) hd) hv) hStar
    _ ≤ (CA + KT * M ^ 2 + LD * M + MA * CV + CStar) * s ^ q := by
      have h1 := mul_le_mul_of_nonneg_left hp (mul_nonneg hKT (sq_nonneg M))
      have h2 := mul_le_mul_of_nonneg_left hp (mul_nonneg hLD hM)
      nlinarith

/-- The normalized transition on a common image disc has a uniform
quantitative first-order expansion. Its moving holomorphic inverse is
constructed in the proof; all inverse and composition estimates are outputs. -/
theorem exists_quantitative_normalized_transition
    (F A : ℝ → ℂ → ℂ) (D DA : ℂ → ℂ) (uStar : ℂ)
    (r q CF CA MF MD MA MDA : ℝ) (hr : 0 < r) (hq : 1 < q) (hq2 : q ≤ 2)
    (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hMF : 0 ≤ MF) (hMD : 0 ≤ MD)
    (hMA : 0 ≤ MA) (hMDA : 0 ≤ MDA) (h00 : F 0 0 = 0)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4))
    (hFa0 : DiffContOnCl ℂ (F 0) (ball (0 : ℂ) (4 * r)))
    (hFa : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (F s) (ball (0 : ℂ) (4 * r)))
    (hDa : DiffContOnCl ℂ D (ball (0 : ℂ) (4 * r)))
    (hAa0 : DiffContOnCl ℂ (A 0) (ball (0 : ℂ) (4 * r)))
    (hDAa : DiffContOnCl ℂ DA (ball (0 : ℂ) (4 * r)))
    (hFb : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖F 0 x‖ ≤ MF)
    (hDb : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖D x‖ ≤ MD)
    (hAb : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖A 0 x‖ ≤ MA)
    (hDAb : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖DA x‖ ≤ MDA)
    (huStar : uStar ∈ closedBall (0 : ℂ) (4 * r))
    (hUniformF : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s x - F 0 x - (s : ℂ) * D x‖ ≤ CF * s ^ q)
    (hUniformA : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ closedBall (0 : ℂ) (4 * r),
      ‖A s x - A 0 x - (s : ℂ) * DA x‖ ≤ CA * s ^ q) :
    ∃ V : ℝ → ℂ → ℂ, ∃ CG ≥ 0,
      (∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z) ∧
      AnalyticOnNhd ℂ (V 0) (ball (0 : ℂ) (r / 4)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ z ∈ ball (0 : ℂ) (r / 4), V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z) ∧
        AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) (r / 4)) ∧
        (∀ z ∈ ball (0 : ℂ) (r / 4),
          ‖(A s (V s z) - A s uStar) - (A 0 (V 0 z) - A 0 uStar) -
            (s : ℂ) * (DA (V 0 z) - DA uStar -
              (deriv (A 0) (V 0 z) / deriv (F 0) (V 0 z)) * D (V 0 z))‖ ≤ CG * s ^ q)) := by
  obtain ⟨V, CV, hCV, hV0, hVa0, hV⟩ := exists_quantitative_inverse_family F D r q CF MF MD
    hr hq hq2 hCF hMF hMD h00 hF0 hFa0 hFa hDa hFb hDb hUniformF
  let M := CV + 2 * MD
  let KT := 2 * MA / r ^ 2
  let LD := MDA / r
  let MB := MA / r
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hKT : 0 ≤ KT := by dsimp [KT]; positivity
  have hLD : 0 ≤ LD := by dsimp [LD]; positivity
  have hMB : 0 ≤ MB := by dsimp [MB]; positivity
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, M * s ≤ r / 2 := by
    have hm : Tendsto (fun s : ℝ => M * s) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).const_mul M).mono_left nhdsWithin_le_nhds
    exact (hm.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < r / 2))).mono fun _ h => h.le
  have hsub : closedBall (0 : ℂ) r ⊆ closedBall (0 : ℂ) (4 * r) := by
    intro x hx
    have hn : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hx
    simp only [mem_closedBall, dist_zero_right]; linarith
  have hsub2 : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) (2 * r) := by
    intro x hx
    have hn : ‖x‖ ≤ r := by simpa [mem_closedBall, dist_zero_right] using hx
    simp only [mem_ball, dist_zero_right]; linarith
  have hhalf : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    intro x hx y hy
    exact (hF0 x hx y hy).trans (by norm_num; nlinarith [norm_nonneg (x-y)])
  have hFa0' : AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) (2 * r)) := by
    intro x hx
    exact hFa0.differentiableOn.analyticAt (isOpen_ball.mem_nhds (by
      simp only [mem_ball, dist_zero_right] at hx ⊢; linarith))
  refine ⟨V, CA + KT * M ^ 2 + LD * M + MB * CV + CA, by positivity, hV0, hVa0, ?_⟩
  filter_upwards [hV, hUniformA, hpos, hle, hsmall] with s hs ha hsp hs1 hsmall
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro z hz
  have hv := hs.1 z hz
  have hv0 := hV0 z hz
  have hBnorm := Kneser.StableHolomorphicInverse.norm_deriv_lower (F 0) r hhalf hFa0'
    (V 0 z) (hsub2 hv0.1)
  have hBinv : ‖deriv (F 0) (V 0 z)‖⁻¹ ≤ (2 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hBnorm
  have hdv : ‖D (V 0 z) / deriv (F 0) (V 0 z)‖ ≤ 2 * MD := by
    rw [norm_div, div_eq_mul_inv]
    exact (mul_le_mul (hDb _ (hsub hv0.1)) hBinv (inv_nonneg.mpr (norm_nonneg _)) hMD).trans_eq (by ring)
  have hmove : ‖V s z - V 0 z‖ ≤ M * s := by
    have hp : s ^ q ≤ s := by simpa using Real.rpow_le_rpow_of_exponent_ge hsp hs1 hq.le
    have heq : V s z - V 0 z =
        (V s z - V 0 z + (s : ℂ) * (D (V 0 z) / deriv (F 0) (V 0 z))) -
          (s : ℂ) * (D (V 0 z) / deriv (F 0) (V 0 z)) := by ring
    rw [heq]
    calc
      _ ≤ ‖V s z - V 0 z + (s : ℂ) * (D (V 0 z) / deriv (F 0) (V 0 z))‖ +
          ‖(s : ℂ) * (D (V 0 z) / deriv (F 0) (V 0 z))‖ := norm_sub_le _ _
      _ ≤ CV * s ^ q + s * (2 * MD) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
        exact add_le_add (hs.2.2 z hz) (mul_le_mul_of_nonneg_left hdv hsp.le)
      _ ≤ M * s := by dsimp [M]; nlinarith [mul_le_mul_of_nonneg_left hp hCV]
  have hSpatial : ‖A 0 (V s z) - A 0 (V 0 z) - deriv (A 0) (V 0 z) * (V s z - V 0 z)‖ ≤
      KT * ‖V s z - V 0 z‖ ^ 2 := by
    convert norm_spatial_first_remainder_le (A 0) r MA hr hMA hAa0 hAb
      (V 0 z) (V s z - V 0 z) hv0.1 (hmove.trans hsmall) using 1
    simp
  have h := norm_normalized_composition_power_remainder s q CA KT LD M MB CV CA
    (A s (V s z)) (A 0 (V s z)) (A 0 (V 0 z)) (DA (V s z)) (DA (V 0 z))
    (deriv (A 0) (V 0 z)) (V s z) (V 0 z) (-D (V 0 z) / deriv (F 0) (V 0 z))
    (A s uStar) (A 0 uStar) (DA uStar) hsp hs1 hq2 hKT hLD hM hMB
    (Kneser.StableHolomorphicInverse.norm_deriv_le_of_disc_bound (A 0) r MA hr hAa0 hAb _ (hsub2 hv0.1))
    (ha _ (hsub hv.1))
    hSpatial
    (norm_sub_le_spatial_lipschitz DA r MDA hr hDAa hDAb (V s z) (V 0 z) hv.1 hv0.1)
    hmove (by simpa only [neg_div, mul_neg, sub_neg_eq_add] using hs.2.2 z hz) (ha _ huStar)
  convert h using 1
  congr 1
  ring

/-- Uniform subtraction of a separately constructed normalization anchor.
The anchor can lie outside the inverse source chart. -/
theorem uniform_subtract_normalization (T : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (K : Set ℂ) (q C : ℝ) (B : ℝ → ℂ) (dB : ℂ) (hC : 0 ≤ C)
    (hT : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ K,
      ‖T s z - T 0 z - (s : ℂ) * D z‖ ≤ C * s ^ q)
    (hB : PowerExpansion B dB q) :
    ∃ CG ≥ 0, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ K,
      ‖(T s z - B s) - (T 0 z - B 0) - (s : ℂ) * (D z - dB)‖ ≤ CG * s ^ q := by
  obtain ⟨CB, hCB, hb⟩ := hB
  refine ⟨C + CB, add_nonneg hC hCB, ?_⟩
  filter_upwards [hT, hb] with s hs hbs
  intro z hz
  have heq : (T s z - B s) - (T 0 z - B 0) - (s : ℂ) * (D z - dB) =
      (T s z - T 0 z - (s : ℂ) * D z) - (B s - B 0 - (s : ℂ) * dB) := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans ((add_le_add (hs z hz) hbs).trans_eq (by ring))

/-- The unnormalized transition also has a uniform expansion. A separate
true real normalization anchor can subsequently be subtracted using the
previous theorem. -/
theorem exists_quantitative_transition
    (F A : ℝ → ℂ → ℂ) (D DA : ℂ → ℂ)
    (r q CF CA MF MD MA MDA : ℝ) (hr : 0 < r) (hq : 1 < q) (hq2 : q ≤ 2)
    (hCF : 0 ≤ CF) (hCA : 0 ≤ CA) (hMF : 0 ≤ MF) (hMD : 0 ≤ MD)
    (hMA : 0 ≤ MA) (hMDA : 0 ≤ MDA) (h00 : F 0 0 = 0)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4))
    (hFa0 : DiffContOnCl ℂ (F 0) (ball (0 : ℂ) (4 * r)))
    (hFa : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (F s) (ball (0 : ℂ) (4 * r)))
    (hDa : DiffContOnCl ℂ D (ball (0 : ℂ) (4 * r)))
    (hAa0 : DiffContOnCl ℂ (A 0) (ball (0 : ℂ) (4 * r)))
    (hDAa : DiffContOnCl ℂ DA (ball (0 : ℂ) (4 * r)))
    (hFb : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖F 0 x‖ ≤ MF)
    (hDb : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖D x‖ ≤ MD)
    (hAb : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖A 0 x‖ ≤ MA)
    (hDAb : ∀ x ∈ closedBall (0 : ℂ) (4 * r), ‖DA x‖ ≤ MDA)
    (hUniformF : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s x - F 0 x - (s : ℂ) * D x‖ ≤ CF * s ^ q)
    (hUniformA : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ closedBall (0 : ℂ) (4 * r),
      ‖A s x - A 0 x - (s : ℂ) * DA x‖ ≤ CA * s ^ q) :
    ∃ V : ℝ → ℂ → ℂ, ∃ CG ≥ 0,
      (∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z) ∧
      AnalyticOnNhd ℂ (V 0) (ball (0 : ℂ) (r / 4)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ z ∈ ball (0 : ℂ) (r / 4), V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z) ∧
        AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) (r / 4)) ∧
        (∀ z ∈ ball (0 : ℂ) (r / 4),
          ‖A s (V s z) - A 0 (V 0 z) -
            (s : ℂ) * (DA (V 0 z) -
              (deriv (A 0) (V 0 z) / deriv (F 0) (V 0 z)) * D (V 0 z))‖ ≤ CG * s ^ q)) := by
  obtain ⟨V, CG, hCG, hV0, hVa0, hV⟩ := exists_quantitative_normalized_transition
    F A D DA 0 r q CF CA MF MD MA MDA hr hq hq2 hCF hCA hMF hMD hMA hMDA h00
    hF0 hFa0 hFa hDa hAa0 hDAa hFb hDb hAb hDAb (by simp; positivity) hUniformF hUniformA
  refine ⟨V, CG + CA, add_nonneg hCG hCA, hV0, hVa0, ?_⟩
  filter_upwards [hV, hUniformA] with s hs ha
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro z hz
  have heq : A s (V s z) - A 0 (V 0 z) -
      (s : ℂ) * (DA (V 0 z) - (deriv (A 0) (V 0 z) / deriv (F 0) (V 0 z)) * D (V 0 z)) =
      ((A s (V s z) - A s 0) - (A 0 (V 0 z) - A 0 0) -
        (s : ℂ) * (DA (V 0 z) - DA 0 -
          (deriv (A 0) (V 0 z) / deriv (F 0) (V 0 z)) * D (V 0 z))) +
      (A s 0 - A 0 0 - (s : ℂ) * DA 0) := by ring
  rw [heq]
  exact (norm_add_le _ _).trans ((add_le_add (hs.2.2 z hz)
    (ha 0 (by simp; positivity))).trans_eq (by ring))

end Kneser.QuantitativeGateTransition

end
