import Kneser.PreparedFiniteHead

/-!
# The first-order moving cutoff for a quadratic prepared residual

Cauchy's formula is applied to each term on its own disc. The fourth-power
term decay cancels the squared disc radius, so a head of length `J` has
remainder `O(s²J)`. With `J=ceil(s^(-2/5))`, actual sum identities give a
`6/5` expansion even for the preparation `q² Γ`.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.N2FirstOrderCutoff

open Kneser.TruncationBounds Kneser.PowerSeriesTail Kneser.PreparedResidualEstimates
open Kneser.PreparedFiniteHead Kneser.ExponentialUnfolding
open Kneser.ParabolicExponentialOrbit Kneser.PerturbedExponentialOrbit
open Filter Set Complex Metric
open scoped Topology BigOperators

theorem head_radius_le_term_radius (c : ℝ) (hc : 0 ≤ c)
    (J k : ℕ) (hk : k < J) :
    c / (2 * (J : ℝ) ^ 2) ≤ c / (2 * ((k : ℝ) + 1) ^ 2) := by
  have hkJ : (k : ℝ) + 1 ≤ (J : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hk
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (k : ℝ) + 1) hkJ 2
  exact div_le_div_of_nonneg_left hc (by positivity) (by linarith)

/-- The actual Cauchy remainder of an individual fourth-power term is
bounded independently of its orbit index. -/
theorem term_remainder_le (f : ℂ → ℂ) (c M : ℝ) (hc : 0 < c) (hM : 0 ≤ M)
    (J k : ℕ) (hk : k < J) (s : ℝ)
    (hf : DiffContOnCl ℂ f (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ z ∈ sphere (0 : ℂ) (c / ((k : ℝ) + 1) ^ 2),
      ‖f z‖ ≤ M / ((k : ℝ) + 1) ^ 4)
    (hs : |s| ≤ c / (2 * (J : ℝ) ^ 2)) :
    ‖f (s : ℂ) - f 0 - s • deriv f 0‖ ≤ (2 * M / c ^ 2) * s ^ 2 := by
  have hs' : ‖(s : ℂ)‖ ≤ (c / ((k : ℝ) + 1) ^ 2) / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, div_div, mul_comm] using
      hs.trans (head_radius_le_term_radius c hc.le J k hk)
  have h := CauchyHeadTaylor.norm_first_remainder_le f (c / ((k : ℝ) + 1) ^ 2)
    (M / ((k : ℝ) + 1) ^ 4) (s : ℂ) (by positivity) (by positivity) hf hbound hs'
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.real_smul] at h ⊢
  apply h.trans_eq
  field_simp

/-- Summing the individual Cauchy remainders gives `s²J`, rather than
the coarser estimate obtained by treating the whole head as one function. -/
theorem finite_head_remainder_le (term : ℂ → ℕ → ℂ) (c M : ℝ)
    (hc : 0 < c) (hM : 0 ≤ M) (J : ℕ) (s : ℝ)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun z => term z k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term z k‖ ≤ M / ((k : ℝ) + 1) ^ 4)
    (hs : |s| ≤ c / (2 * (J : ℝ) ^ 2)) :
    ‖∑ k ∈ Finset.range J,
      (term (s : ℂ) k - term 0 k - s • deriv (fun z => term z k) 0)‖ ≤
      (2 * M / c ^ 2) * s ^ 2 * (J : ℝ) := by
  calc
    _ ≤ ∑ k ∈ Finset.range J,
        ‖term (s : ℂ) k - term 0 k - s • deriv (fun z => term z k) 0‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range J, (2 * M / c ^ 2) * s ^ 2 := by
      apply Finset.sum_le_sum
      intro k hk
      exact term_remainder_le (fun z => term z k) c M hc hM J k
        (Finset.mem_range.mp hk) s (hdisc k)
        (fun z hz => hbound k z (by
          have hn : ‖z‖ = c / ((k : ℝ) + 1) ^ 2 := by
            simpa only [mem_sphere, dist_zero_right] using hz
          exact hn.le)) hs
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

theorem hasDerivAt_term (term : ℂ → ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun z => term z k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2))) (k : ℕ) :
    HasDerivAt (fun z => term z k) (deriv (fun z => term z k) 0) 0 := by
  exact ((hdisc k).differentiableOn.differentiableAt
    (isOpen_ball.mem_nhds (by simp only [mem_ball, dist_self]; positivity))).hasDerivAt

/-- The derivative majorant is also a Cauchy conclusion. -/
theorem norm_deriv_term_le (term : ℂ → ℕ → ℂ) (c M : ℝ) (hc : 0 < c)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun z => term z k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term z k‖ ≤ M / ((k : ℝ) + 1) ^ 4) (k : ℕ) :
    ‖deriv (fun z => term z k) 0‖ ≤ (M / c) / ((k : ℝ) + 1) ^ 2 := by
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := (0 : ℂ)) (by positivity : 0 < c / ((k : ℝ) + 1) ^ 2) (hdisc k)
    (fun z hz => hbound k z (by
      have hn : ‖z‖ = c / ((k : ℝ) + 1) ^ 2 := by
        simpa only [mem_sphere, dist_zero_right] using hz
      exact hn.le))
  apply h.trans_eq
  field_simp

theorem head_cutoff_bound {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    s ^ (2 : ℕ) * (cutoff s (2 / 5) : ℝ) ≤ 2 * s ^ (6 / 5 : ℝ) := by
  have h := cutoff_head_bound (β := 2 / 5) (a := 1) (b := 2) hs hs1
    (by norm_num) (by norm_num)
  norm_num [Real.rpow_natCast] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hs hs1 (by norm_num : (6 / 5 : ℝ) ≤ 8 / 5))
    (by norm_num : (0 : ℝ) ≤ 2))

theorem norm_tail_cutoff (a : ℕ → ℂ) (C s : ℝ) (hC : 0 ≤ C) (hs : 0 < s)
    (ha : ∀ k, ‖a k‖ ≤ C / ((k : ℝ) + 1) ^ 4) :
    ‖∑' k : ℕ, a (k + cutoff s (2 / 5))‖ ≤
      (C * powerConstant 4) * s ^ (6 / 5 : ℝ) := by
  have h := norm_tsum_tail_le a C hC (by norm_num) ha (cutoff s (2 / 5)) (cutoff_pos hs)
  have ht := cutoff_tail_bound (β := 2 / 5) (d := 3) hs (by norm_num)
  rw [Real.rpow_neg (by positivity)] at ht
  norm_num [Real.rpow_natCast] at ht
  apply h.trans
  simpa only [show (4 : ℕ) - 1 = 3 from rfl, div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left ht (mul_nonneg hC (powerConstant_nonneg 4))

theorem norm_scaled_derivative_tail_cutoff (δ : ℕ → ℂ) (C s : ℝ)
    (hC : 0 ≤ C) (hs : 0 < s) (hs1 : s ≤ 1)
    (hδ : ∀ k, ‖δ k‖ ≤ C / ((k : ℝ) + 1) ^ 2) :
    ‖s • (∑' k : ℕ, δ (k + cutoff s (2 / 5)))‖ ≤
      (C * powerConstant 2) * s ^ (6 / 5 : ℝ) := by
  have h := norm_tsum_tail_le δ C hC (by norm_num) hδ (cutoff s (2 / 5)) (cutoff_pos hs)
  have ht := cutoff_scaled_tail_bound (β := 2 / 5) (d := 1) (b := 1) hs (by norm_num)
  rw [Real.rpow_neg (by positivity)] at ht
  norm_num [Real.rpow_one] at ht
  have ht' := ht.trans (Real.rpow_le_rpow_of_exponent_ge hs hs1
    (by norm_num : (6 / 5 : ℝ) ≤ 7 / 5))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  calc
    _ ≤ s * (C * powerConstant 2 / (cutoff s (2 / 5) : ℝ) ^ (2 - 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left h hs.le
    _ = (C * powerConstant 2) * (s * (cutoff s (2 / 5) : ℝ)⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ht' (mul_nonneg hC (powerConstant_nonneg 2))

/-- Fourth-power term estimates on their own analytic discs suffice for
the actual `6/5` expansion, with an absolutely convergent actual derivative sum. -/
theorem coordinate_expansion_from_term_discs
    (ψ : ℂ → ℂ) (term : ℂ → ℕ → ℂ) (r Mψ c M CT : ℝ)
    (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hc : 0 < c) (hM : 0 ≤ M) (hCT : 0 ≤ CT)
    (hψ : DiffContOnCl ℂ ψ (ball 0 r))
    (hψbound : ∀ z ∈ sphere (0 : ℂ) r, ‖ψ z‖ ≤ Mψ)
    (hdisc : ∀ k, DiffContOnCl ℂ (fun z => term z k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)))
    (hbound : ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖term z k‖ ≤ M / ((k : ℝ) + 1) ^ 4)
    (hterms : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖term (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 4) :
    let δ := fun k => deriv (fun z => term z k) 0
    let A := coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ))
    let d := firstOrderCoefficient (deriv ψ 0) δ
    (∀ᶠ s : ℝ in 𝓝[>] 0, ‖A s - A 0 - s • d‖ ≤
      (2 * Mψ / r ^ 2 + 4 * M / c ^ 2 +
        2 * (M + CT) * powerConstant 4 + (M / c) * powerConstant 2) * s ^ (6 / 5 : ℝ)) ∧
      HasDerivWithinAt A d (Ici 0) 0 := by
  dsimp only
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < r / 2 :=
    (eventually_lt_nhds (by positivity : (0 : ℝ) < r / 2)).filter_mono nhdsWithin_le_nhds
  have hadmissible := cutoff_admissible (β := 2 / 5) (by norm_num) (by norm_num) hc
  have hδbound := norm_deriv_term_le term c M hc hdisc hbound
  have hzero : ∀ k, ‖term 0 k‖ ≤ (M + CT) / ((k : ℝ) + 1) ^ 4 := by
    intro k
    exact (hbound k 0 (by simp; positivity)).trans
      (div_le_div_of_nonneg_right (le_add_of_nonneg_right hCT) (by positivity))
  have hterms' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖term (s : ℂ) k‖ ≤ (M + CT) / ((k : ℝ) + 1) ^ 4 := by
    filter_upwards [hterms] with s hs
    intro k
    exact (hs k).trans (div_le_div_of_nonneg_right (le_add_of_nonneg_left hM) (by positivity))
  have hmodel : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖ψ (s : ℂ) - ψ 0 - s • deriv ψ 0‖ ≤ (2 * Mψ / r ^ 2) * s ^ (6 / 5 : ℝ) := by
    filter_upwards [hpos, hle, hsmall] with s hs hs1 hsr
    have hb := CauchyHeadTaylor.norm_first_remainder_le ψ r Mψ (s : ℂ) hr hMψ hψ hψbound
      (by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsr.le)
    have hp := Real.rpow_le_rpow_of_exponent_ge hs hs1 (show (6 / 5 : ℝ) ≤ 2 by norm_num)
    norm_num [Real.rpow_natCast] at hp
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs, Complex.real_smul] at hb ⊢
    apply hb.trans
    convert mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 2 * Mψ / r ^ 2) using 1
    ring
  have hhead : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖∑ k ∈ Finset.range (cutoff s (2 / 5)),
        (term (s : ℂ) k - term 0 k - s • deriv (fun z => term z k) 0)‖ ≤
        (4 * M / c ^ 2) * s ^ (6 / 5 : ℝ) := by
    filter_upwards [hpos, hle, hadmissible] with s hs hs1 ha
    have hb := finite_head_remainder_le term c M hc hM (cutoff s (2 / 5)) s hdisc hbound
      (by simpa only [abs_of_pos hs] using ha)
    apply hb.trans
    convert mul_le_mul_of_nonneg_left (head_cutoff_bound hs hs1)
      (by positivity : 0 ≤ 2 * M / c ^ 2) using 1 <;> ring
  have htail : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖∑' k : ℕ, term (s : ℂ) (k + cutoff s (2 / 5))‖ ≤
        ((M + CT) * powerConstant 4) * s ^ (6 / 5 : ℝ) := by
    filter_upwards [hpos, hterms'] with s hs ht
    exact norm_tail_cutoff _ _ _ (add_nonneg hM hCT) hs ht
  have htailzero : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖∑' k : ℕ, term 0 (k + cutoff s (2 / 5))‖ ≤
        ((M + CT) * powerConstant 4) * s ^ (6 / 5 : ℝ) := by
    filter_upwards [hpos] with s hs
    exact norm_tail_cutoff _ _ _ (add_nonneg hM hCT) hs hzero
  have htailδ : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖s • (∑' k : ℕ, deriv (fun z => term z (k + cutoff s (2 / 5))) 0)‖ ≤
        ((M / c) * powerConstant 2) * s ^ (6 / 5 : ℝ) := by
    filter_upwards [hpos, hle] with s hs hs1
    exact norm_scaled_derivative_tail_cutoff _ _ _ (by positivity) hs hs1 hδbound
  have hsummable : ∀ᶠ s : ℝ in 𝓝[>] 0, Summable (term (s : ℂ)) := by
    filter_upwards [hterms'] with s hs
    exact summable_of_parabolic_bound _ (M + CT) (by norm_num) hs
  have he := coordinateSeries_power_error (fun s : ℝ => ψ (s : ℂ))
    (fun s : ℝ => term (s : ℂ)) (deriv ψ 0) (fun k => deriv (fun z => term z k) 0)
    (fun s => cutoff s (2 / 5)) (2 * Mψ / r ^ 2) (4 * M / c ^ 2)
    ((M + CT) * powerConstant 4) ((M / c) * powerConstant 2) (6 / 5)
    (summable_of_parabolic_bound _ (M + CT) (by norm_num) hzero)
    (summable_norm_of_parabolic_bound _ (M / c) (by norm_num) hδbound)
    hsummable hmodel hhead htail htailzero htailδ
  have he' : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) s -
        coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ)) 0 -
        s • firstOrderCoefficient (deriv ψ 0) (fun k => deriv (fun z => term z k) 0)‖ ≤
        (2 * Mψ / r ^ 2 + 4 * M / c ^ 2 +
          2 * (M + CT) * powerConstant 4 + (M / c) * powerConstant 2) * s ^ (6 / 5 : ℝ) := by
    filter_upwards [he] with s hs
    convert hs using 1
    ring
  exact ⟨he', hasDerivWithinAt_of_power_error _ _ _ (6 / 5) (by norm_num) he'⟩

/-- The actual `q²Γ` preparation satisfies the hypotheses of the sharpened
cutoff theorem, with no finite-head or derivative-bound inputs. -/
theorem prepared_quadratic_coordinate_expansion
    (ψ : ℂ → ℂ) (q Γ : ℂ × ℂ → ℂ) (u : ℂ)
    (R Z Cq M r Mψ CT : ℝ) (hR : 64 ≤ R)
    (hu : R ≤ (inverseCoordinate u).re) (hZ : ‖inverseCoordinate u‖ ≤ Z)
    (hCq : 0 ≤ Cq) (hM : 0 ≤ M) (hr : 0 < r) (hMψ : 0 ≤ Mψ) (hCT : 0 ≤ CT)
    (hq : DifferentiableOn ℂ q (preparationPolydisc Z))
    (hΓ : DifferentiableOn ℂ Γ (preparationPolydisc Z))
    (hqBound : ∀ p ∈ preparationPolydisc Z, ‖q p‖ ≤ ‖p.2‖ ^ 2 + Cq * ‖p.1‖)
    (hΓBound : ∀ p ∈ preparationPolydisc Z, ‖Γ p‖ ≤ M)
    (hψ : DiffContOnCl ℂ ψ (ball 0 r))
    (hψbound : ∀ z ∈ sphere (0 : ℂ) r, ‖ψ z‖ ≤ Mψ)
    (hterms : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ k,
      ‖preparedTerm q Γ 2 u (s : ℂ) k‖ ≤ CT / ((k : ℝ) + 1) ^ 4) :
    let term := preparedTerm q Γ 2 u
    let δ := fun k => deriv (fun z => term z k) 0
    let A := coordinateSeries (fun s : ℝ => ψ (s : ℂ)) (fun s : ℝ => term (s : ℂ))
    let d := firstOrderCoefficient (deriv ψ 0) δ
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ‖A s - A 0 - s • d‖ ≤ C * s ^ (6 / 5 : ℝ)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ‖A s - A 0 - s • d‖ ≤ C * s ^ (10 / 9 : ℝ)) ∧
      HasDerivWithinAt A d (Ici 0) 0 := by
  dsimp only
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  let c := parameterRadius Z 0
  have hc : 0 < c := parameterRadius_pos Z hZ0 0
  let C0 := M * (16 + Cq * c) ^ 2
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hdisc : ∀ k, DiffContOnCl ℂ (fun z => preparedTerm q Γ 2 u z k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)) := by
    intro k
    rw [← parameterRadius_eq Z k]
    exact ((differentiableOn_prepared_orbit q Γ 2 u R Z hR hu hZ hq hΓ k).mono
      closure_ball_subset_closedBall).diffContOnCl
  have hbound : ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
      ‖preparedTerm q Γ 2 u z k‖ ≤ C0 / ((k : ℝ) + 1) ^ 4 := by
    intro k z hz
    exact norm_prepared_orbit_le q Γ 2 u z R Z Cq M hR hu hZ hCq hM hqBound hΓBound k
      (by simpa only [parameterRadius_eq Z k] using hz)
  have h := coordinate_expansion_from_term_discs ψ (preparedTerm q Γ 2 u)
    r Mψ c C0 CT hr hMψ hc hC0 hCT hψ hψbound hdisc hbound hterms
  let C := 2 * Mψ / r ^ 2 + 4 * C0 / c ^ 2 +
    2 * (C0 + CT) * powerConstant 4 + (C0 / c) * powerConstant 2
  have hC : 0 ≤ C := by
    have hp4 := powerConstant_nonneg 4
    have hp2 := powerConstant_nonneg 2
    dsimp [C]
    positivity
  refine ⟨C, hC, h.1, ?_, h.2⟩
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ hs => hs.le).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [h.1, hpos, hle] with s hs hspos hs1
  exact hs.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hspos hs1 (by norm_num : (10 / 9 : ℝ) ≤ 6 / 5)) hC)

end Kneser.N2FirstOrderCutoff

end
