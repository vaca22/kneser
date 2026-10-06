import Kneser.ActualRootPolynomialOrbit
import Kneser.RepellingRealPetal

/-! Actual infinite-orbit preparation bounds for the reflected inverse family. -/

noncomputable section

namespace Kneser.ReflectedPreparedRealMajorant

open Filter Kneser.ExponentialUnfolding Kneser.ExponentialRootPolynomial
open Kneser.ParabolicExponentialOrbit (inverseCoordinate)
open Kneser.RepellingExponentialOrbit Kneser.RepellingRealPetal
open Kneser.ActualRootPolynomialOrbit (rootPolynomial_eq_real_root_product norm_le_of_root_product_bound)
open scoped Topology

/-- The actual factorization and its nonzero cofactor at the parabolic point
yield the complete positive-parameter orbit estimate on every bounded,
buffered parabolic petal, together with containment in any chosen disc. -/
theorem eventually_actual_rootPolynomial_orbit_bound
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) (0, 0))
    (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∀ u : ℂ, R + 1 ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
          ∀ k : ℕ, ‖rootPolynomial A B s (-inverseOrbit u s k)‖ ≤
              100 / (R + (3 / 4) * (k : ℝ)) ^ 2 ∧
            ‖-inverseOrbit u s k‖ < ρ := by
  have hKnz : ∀ᶠ p in 𝓝 ((0, 0) : ℂ × ℂ), K p.1 p.2 ≠ 0 :=
    hK.eventually (eventually_ne_nhds hK0)
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.mp hKnz
  obtain ⟨r, hr, hrball⟩ := Metric.eventually_nhds_iff.mp hfactor
  obtain ⟨R₁, hR₁, hpetals⟩ := exists_uniform_initial_repelling_petals
  refine ⟨max R₁ (20 / ρ), lt_of_lt_of_le hR₁ (le_max_left _ _), ?_⟩
  intro R hR Z hZ
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hRρ : 20 / ρ ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := hR₁.trans_le hRR₁
  let δ : ℝ := min η (ρ / 4)
  have hδ : 0 < δ := lt_min hη (by positivity)
  let W : ℝ := max Z (1 / δ)
  have hW : 0 ≤ W := le_trans hZ (le_max_left _ _)
  have hWZ : Z ≤ W := le_max_left _ _
  have hWδ : 1 / δ ≤ W := le_max_right _ _
  have hδW : 1 ≤ δ * W := by
    have h := (div_le_iff₀ hδ).mp hWδ
    nlinarith
  have hrootδ : 1 / (4 * (W + 1)) < δ := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  obtain ⟨s₁, hs₁, hs₁half, hroots⟩ := hpetals R hRR₁ W hW
  refine ⟨min s₁ (min η r), lt_min hs₁ (lt_min hη hr), ?_⟩
  intro s hs hss u hu hZu k
  have hs₁' : s < s₁ := hss.trans_le (min_le_left _ _)
  have hsη : s < η := hss.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsr : s < r := hss.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨a, b, θ, ha, hb, haW, hbW, hθ, hfa, hfb, hθeq, horbit⟩ :=
    hroots s hs hs₁'
  have haδ : |a| < δ := haW.trans hrootδ
  have hbδ : |b| < δ := hbW.trans hrootδ
  have hKa : K s a ≠ 0 := by
    apply hηball (y := ((s : ℂ), (a : ℂ)))
    simp only [Prod.dist_eq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact max_lt (by simpa [abs_of_pos hs] using hsη)
      (haδ.trans_le (min_le_left _ _))
  have hKb : K s b ≠ 0 := by
    apply hηball (y := ((s : ℂ), (b : ℂ)))
    simp only [Prod.dist_eq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    exact max_lt (by simpa [abs_of_pos hs] using hsη)
      (hbδ.trans_le (min_le_left _ _))
  have hsr' : dist (s : ℂ) 0 < r := by
    simpa [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] using hsr
  have hfs := hrball hsr'
  have hq := rootPolynomial_eq_real_root_product A B K s a b
    (by linarith) hfs hfa hfb hKa hKb (-inverseOrbit u s k)
  have hpinv := (horbit u hu (hZu.trans hWZ)).2 k
  have hp : ‖-inverseOrbit u s k - (a : ℂ)‖ * ‖-inverseOrbit u s k - (b : ℂ)‖ ≤
      100 / (R + (3 / 4) * (k : ℝ)) ^ 2 := by
    have heqa : -inverseOrbit u s k - (a : ℂ) = -(inverseOrbit u s k + (a : ℂ)) := by ring
    have heqb : -inverseOrbit u s k - (b : ℂ) = -(inverseOrbit u s k + (b : ℂ)) := by ring
    rw [heqa, heqb, norm_neg, norm_neg, mul_comm]
    exact hpinv
  refine ⟨by simpa only [hq, norm_mul] using hp, ?_⟩
  apply norm_le_of_root_product_bound (-inverseOrbit u s k) (a : ℂ) b ρ
    (100 / (R + (3 / 4) * (k : ℝ)) ^ 2) hρ
    (by simpa [Complex.norm_real, Real.norm_eq_abs] using
      haδ.le.trans (min_le_right _ _))
    (by simpa [Complex.norm_real, Real.norm_eq_abs] using
      hbδ.le.trans (min_le_right _ _)) _ hp
  have hden : 0 < R + (3 / 4) * (k : ℝ) := by positivity
  apply (div_lt_iff₀ (sq_pos_of_pos hden)).mpr
  have hmul : 20 ≤ R * ρ := (div_le_iff₀ hρ).mp hRρ
  have hmulden : 20 ≤ (R + (3 / 4) * (k : ℝ)) * ρ := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  nlinarith [sq_nonneg ((R + (3 / 4) * (k : ℝ)) * ρ - 20)]

/-- The infinite positive-real residual majorant follows from continuity of
the actual preparation factor and the actual dynamical estimates. -/
theorem exists_actual_prepared_real_majorant
    (A B : ℂ → ℂ) (K : ℂ → ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (hK : ContinuousAt (fun p : ℂ × ℂ => K p.1 p.2) (0, 0))
    (hK0 : K 0 0 ≠ 0)
    (hfactor : ∀ᶠ s in 𝓝 (0 : ℂ), ∀ u,
      unfolding s u - u = rootPolynomial A B s u * K s u)
    (hΓ : ContinuousAt Γ 0) :
    ∃ R₀ C : ℝ, 0 < R₀ ∧ 0 ≤ C ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s < s₀ →
        ∀ u : ℂ, R + 1 ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
          ∀ k : ℕ,
            ‖PreparedResidualEstimates.preparedResidual
              (fun p => rootPolynomial A B p.1 p.2) Γ N s (-inverseOrbit u s k)‖ ≤
              C / ((k : ℝ) + 1) ^ (2 * N) := by
  let M : ℝ := ‖Γ 0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hΓb : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), ‖Γ p‖ < M :=
    hΓ.norm.eventually (gt_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.mp hΓb
  let ρ : ℝ := η / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨R₁, hR₁, horbits⟩ :=
    eventually_actual_rootPolynomial_orbit_bound A B K hK hK0 hfactor ρ hρ
  refine ⟨max R₁ 1, M * 400 ^ N, lt_of_lt_of_le hR₁ (le_max_left _ _),
    by positivity, ?_⟩
  intro R hR Z hZ
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hRone : 1 ≤ R := (le_max_right _ _).trans hR
  obtain ⟨s₁, hs₁, hactual⟩ := horbits R hRR₁ Z hZ
  refine ⟨min s₁ ρ, lt_min hs₁ hρ, ?_⟩
  intro s hs hss u hu hZu k
  obtain ⟨hq, hv⟩ := hactual s hs (hss.trans_le (min_le_left _ _)) u hu hZu k
  have hsρ : s < ρ := hss.trans_le (min_le_right _ _)
  have hΓv : ‖Γ ((s : ℂ), -inverseOrbit u s k)‖ ≤ M := by
    apply (hηball (y := ((s : ℂ), -inverseOrbit u s k)) _).le
    have hηρ : ρ < η := by dsimp [ρ]; linarith
    simpa only [dist_zero_right, Prod.norm_def, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hs] using max_lt (hsρ.trans hηρ) (hv.trans hηρ)
  have hden : 0 < R + (3 / 4) * (k : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hl : ((k : ℝ) + 1) / 2 ≤ R + (3 / 4) * (k : ℝ) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hq' : ‖rootPolynomial A B s (-inverseOrbit u s k)‖ ≤ 400 / ((k : ℝ) + 1) ^ 2 := by
    apply hq.trans
    calc
      100 / (R + (3 / 4) * (k : ℝ)) ^ 2 ≤ 100 / (((k : ℝ) + 1) / 2) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_left₀ (by positivity) hl 2)
      _ = _ := by field_simp; ring
  rw [PreparedResidualEstimates.preparedResidual, norm_mul, norm_pow]
  calc
    _ ≤ (400 / ((k : ℝ) + 1) ^ 2) ^ N * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hq' N) hΓv (norm_nonneg _)
        (by positivity)
    _ = _ := by rw [div_pow, ← pow_mul]; ring

end Kneser.ReflectedPreparedRealMajorant

end
