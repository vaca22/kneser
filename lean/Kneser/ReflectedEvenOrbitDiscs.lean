import Kneser.AnalyticEvenDescent
import Kneser.RepellingExponentialOrbit
import Kneser.AnalyticRootBounds
import Kneser.PreparedResidualEstimates

/-!
The actual prepared factor is analytic in the splitting coordinate `x`, with
`s=x²`.  Evenness makes the descended orbit term holomorphic across `s=0`
and across the principal square-root cut.  The parameter discs and their
residual bounds are derived from the genuine finite exponential orbits.
-/

noncomputable section

namespace Kneser.ReflectedEvenOrbitDiscs

open Filter Set Metric Kneser.ExponentialUnfolding
open Kneser.ExponentialRootPolynomial
open Kneser.ParabolicExponentialOrbit (inverseCoordinate)
open Kneser.RepellingExponentialOrbit
open Kneser.PerturbedExponentialOrbit (parameterRadius parameterRadius_pos)
open Kneser.PreparedResidualEstimates (preparedResidual parameterRadius_eq)
open scoped Topology

theorem finite_inverseOrbit_norm_le_four_div (u s : ℂ) (R Z : ℝ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (k : ℕ)
    (hs : ‖s‖ ≤ parameterRadius Z k) :
    ‖inverseOrbit u s k‖ ≤ 4 / ((k : ℝ) + 1) := by
  have horbit := finite_inverseOrbit_norm_bound_of_upper_bound u s R Z hR hu hZ k hs k (le_refl k)
  apply horbit.trans
  apply (div_le_div_iff₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)).mpr
  linarith

def descendedFactor (Γ : ℂ × ℂ → ℂ) (p : ℂ × ℂ) : ℂ :=
  Γ (Complex.sqrt p.1, p.2)

def splitTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (u : ℂ)
    (x : ℂ) (k : ℕ) : ℂ :=
  rootPolynomial A B (x ^ 2) (-inverseOrbit u (x ^ 2) k) ^ N *
    Γ (x, -inverseOrbit u (x ^ 2) k)

def descendedTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (u : ℂ)
    (s : ℂ) (k : ℕ) : ℂ := splitTerm A B Γ N u (Complex.sqrt s) k

theorem descendedTerm_eq (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u s : ℂ) (k : ℕ) :
    descendedTerm A B Γ N u s k =
      preparedResidual (fun p => rootPolynomial A B p.1 p.2)
        (descendedFactor Γ) N s (-inverseOrbit u s k) := by
  simp [descendedTerm, splitTerm, preparedResidual, descendedFactor]

theorem even_splitTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (u : ℂ)
    (hΓ : ∀ x v, Γ (-x, v) = Γ (x, v)) (k : ℕ) (x : ℂ) :
    splitTerm A B Γ N u (-x) k = splitTerm A B Γ N u x k := by
  simp only [splitTerm, neg_sq, hΓ]

theorem analyticAt_splitTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u x : ℂ) (k : ℕ) (hA : AnalyticAt ℂ A (x ^ 2))
    (hB : AnalyticAt ℂ B (x ^ 2))
    (hΓ : AnalyticAt ℂ Γ (x, -inverseOrbit u (x ^ 2) k))
    (hOrbit : AnalyticAt ℂ (fun s => inverseOrbit u s k) (x ^ 2)) :
    AnalyticAt ℂ (fun y => splitTerm A B Γ N u y k) x := by
  have hs : AnalyticAt ℂ (fun y : ℂ => y ^ 2) x := analyticAt_id.pow 2
  have ho : AnalyticAt ℂ (fun y => -inverseOrbit u (y ^ 2) k) x :=
    (hOrbit.comp_of_eq hs rfl).neg
  exact (((ho.pow 2).sub ((hA.comp_of_eq hs rfl).mul ho)).add (hB.comp_of_eq hs rfl)).pow N |>.mul
    (hΓ.comp_of_eq (analyticAt_id.prod ho) rfl)

theorem analyticAt_descendedTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (u s : ℂ) (k : ℕ) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v))
    (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s)
    (hΓ : AnalyticAt ℂ Γ (Complex.sqrt s, -inverseOrbit u s k))
    (hOrbit : AnalyticAt ℂ (fun t => inverseOrbit u t k) s) :
    AnalyticAt ℂ (fun z => descendedTerm A B Γ N u z k) s := by
  have hsplit : AnalyticAt ℂ (fun y => splitTerm A B Γ N u y k) (Complex.sqrt s) := by
    apply analyticAt_splitTerm
    · simpa using hA
    · simpa using hB
    · simpa using hΓ
    · simpa using hOrbit
  by_cases hs : s = 0
  · subst s
    exact AnalyticEvenDescent.analyticAt_even_sqrt (even_splitTerm A B Γ N u hEven k)
      (by simpa using hsplit)
  · exact AnalyticEvenDescent.analyticAt_even_sqrt_of_ne (even_splitTerm A B Γ N u hEven k)
      hs hsplit

theorem continuousAt_descendedFactor (Γ : ℂ × ℂ → ℂ)
    (hΓ : ContinuousAt Γ 0) : ContinuousAt (descendedFactor Γ) 0 := by
  have hsqrt : ContinuousAt Complex.sqrt 0 := Complex.continuousAt_sqrt (Or.inl (by simp))
  have hp : ContinuousAt (fun p : ℂ × ℂ => (Complex.sqrt p.1, p.2)) 0 :=
    (hsqrt.comp_of_eq continuous_fst.continuousAt rfl).prodMk continuous_snd.continuousAt
  exact hΓ.comp_of_eq hp (by simp)

theorem finite_orbit_graph_small (u s : ℂ) (R Z η c : ℝ) (k : ℕ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (hη : 0 < η) (hRη : 4 / η ≤ R)
    (hcZ : c < parameterRadius Z 0) (hcη : c ≤ η ^ 2 / 4)
    (hs : ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2) :
    ‖(Complex.sqrt s, -inverseOrbit u s k)‖ < η := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans hZ
  have hden : 1 ≤ ((k : ℝ) + 1) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have hsp : ‖s‖ ≤ parameterRadius Z k := by
    rw [parameterRadius_eq]
    exact hs.trans (div_le_div_of_nonneg_right hcZ.le (by positivity))
  have hsc : ‖s‖ ≤ c := by
    have hc : 0 ≤ c := by
      have h := (le_div_iff₀ (by positivity : 0 < ((k : ℝ) + 1) ^ 2)).mp hs
      nlinarith [norm_nonneg s]
    exact hs.trans (div_le_self hc hden)
  have hsq : ‖Complex.sqrt s‖ ^ 2 = ‖s‖ := by
    rw [← norm_pow, AnalyticEvenDescent.square_sqrt]
  have hxs : ‖Complex.sqrt s‖ ≤ η / 2 := by
    nlinarith [norm_nonneg (Complex.sqrt s)]
  have hv := finite_inverseOrbit_norm_bound_of_upper_bound u s R Z hR hu hZ k hsp k (le_refl k)
  have hdenR : 0 < R + (k : ℝ) / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hRmul : 4 ≤ R * η := (div_le_iff₀ hη).mp hRη
  have hvη : ‖inverseOrbit u s k‖ ≤ η / 2 := by
    apply hv.trans
    apply (div_le_iff₀ hdenR).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  rw [Prod.norm_def, norm_neg]
  exact max_lt (lt_of_le_of_lt hxs (by linarith)) (lt_of_le_of_lt hvη (by linarith))

/-- Holomorphy on the full parameter disc comes from actual analytic even
preparation in the splitting variable, including the square-root cut. -/
theorem diffContOnCl_descendedTerm
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (u : ℂ) (R Z η r c : ℝ)
    (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (hη : 0 < η) (hRη : 4 / η ≤ R)
    (hc : 0 < c) (hcZ : c < parameterRadius Z 0) (hcη : c ≤ η ^ 2 / 4)
    (hcr : c < r)
    (hA : ∀ s : ℂ, ‖s‖ < r → AnalyticAt ℂ A s)
    (hB : ∀ s : ℂ, ‖s‖ < r → AnalyticAt ℂ B s)
    (hΓ : ∀ p : ℂ × ℂ, ‖p‖ < η → AnalyticAt ℂ Γ p)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) (k : ℕ) :
    DiffContOnCl ℂ (fun z => descendedTerm A B Γ N u z k)
      (ball 0 (c / ((k : ℝ) + 1) ^ 2)) := by
  have hd : DifferentiableOn ℂ (fun z => descendedTerm A B Γ N u z k)
      (closedBall 0 (c / ((k : ℝ) + 1) ^ 2)) := by
    intro s hs
    have hsn : ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 := by
      simpa [mem_closedBall, dist_zero_right] using hs
    have hsc : ‖s‖ ≤ c := hsn.trans (div_le_self hc.le (by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]))
    exact (analyticAt_descendedTerm A B Γ N u s k hEven
      (hA s (hsc.trans_lt hcr)) (hB s (hsc.trans_lt hcr))
      (hΓ _ (finite_orbit_graph_small u s R Z η c k hR hu hZ hη hRη hcZ hcη hsn))
      (analyticAt_inverseOrbit_parameter u s R Z hR hu hZ k (by
        rw [parameterRadius_eq]
        exact hsn.trans_lt (div_lt_div_of_pos_right hcZ (by positivity))) k (le_refl k))).differentiableAt.differentiableWithinAt
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl

theorem norm_descendedTerm_le
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ) (u s : ℂ)
    (R Z η r c Cq M : ℝ) (hR : 64 ≤ R) (hu : R ≤ (inverseCoordinate u).re)
    (hZ : ‖inverseCoordinate u‖ ≤ Z) (hη : 0 < η) (hRη : 4 / η ≤ R)
    (hc : 0 < c) (hcZ : c < parameterRadius Z 0) (hcη : c ≤ η ^ 2 / 4)
    (hcr : c < r) (hCq : 0 ≤ Cq) (_hM : 0 ≤ M)
    (hq : ∀ s v : ℂ, ‖s‖ < r → ‖v‖ ≤ 1 / 2 →
      ‖rootPolynomial A B s v‖ ≤ ‖v‖ ^ 2 + Cq * ‖s‖)
    (hΓ : ∀ p : ℂ × ℂ, ‖p‖ < η → ‖Γ p‖ ≤ M)
    (k : ℕ) (hs : ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2) :
    ‖descendedTerm A B Γ N u s k‖ ≤
      M * (16 + Cq * c) ^ N / ((k : ℝ) + 1) ^ (2 * N) := by
  have hsp : ‖s‖ ≤ parameterRadius Z k := by
    rw [parameterRadius_eq]
    exact hs.trans (div_le_div_of_nonneg_right hcZ.le (by positivity))
  have hsc : ‖s‖ ≤ c := hs.trans (div_le_self hc.le (by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]))
  have ho := finite_inverseOrbit_norm_le_four_div u s R Z hR hu hZ k hsp
  have hov := finite_inverseOrbit_norm_bound_of_upper_bound u s R Z hR hu hZ k hsp k (le_refl k)
  have hovhalf : ‖-inverseOrbit u s k‖ ≤ 1 / 2 := by
    rw [norm_neg]
    apply hov.trans
    apply (div_le_iff₀ (by linarith [Nat.cast_nonneg (α := ℝ) k] :
      0 < R + (k : ℝ) / 2)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hqp : ‖rootPolynomial A B s (-inverseOrbit u s k)‖ ≤
      (16 + Cq * c) / ((k : ℝ) + 1) ^ 2 := by
    apply (hq s _ (hsc.trans_lt hcr) hovhalf).trans
    calc
      _ ≤ (4 / ((k : ℝ) + 1)) ^ 2 + Cq * (c / ((k : ℝ) + 1) ^ 2) :=
        add_le_add (pow_le_pow_left₀ (norm_nonneg _) (by simpa only [norm_neg] using ho) 2)
          (mul_le_mul_of_nonneg_left hs hCq)
      _ = _ := by field_simp; ring
  have hΓv := hΓ _ (finite_orbit_graph_small u s R Z η c k hR hu hZ hη hRη hcZ hcη hs)
  simp only [descendedTerm, splitTerm, AnalyticEvenDescent.square_sqrt, norm_mul, norm_pow]
  calc
    _ ≤ ((16 + Cq * c) / ((k : ℝ) + 1) ^ 2) ^ N * M :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hqp N) hΓv (norm_nonneg _)
        (by positivity)
    _ = _ := by rw [div_pow, ← pow_mul]; ring

/-- All local preparation-disc and Cauchy bounds are obtained from analytic
germs; neither a uniform orbit-disc radius nor a residual estimate is input. -/
theorem exists_prepared_orbit_disc_bounds
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∀ u : ℂ, R ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
        ∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧
          (∀ k, DiffContOnCl ℂ (fun z => descendedTerm A B Γ N u z k)
            (ball 0 (c / ((k : ℝ) + 1) ^ 2))) ∧
          (∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
            ‖descendedTerm A B Γ N u z k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) := by
  obtain ⟨r₁, Cq, hr₁, hCq, hqbound⟩ :=
    AnalyticRootBounds.rootPolynomial_norm_bound hAa hBa hA0 hB0
  obtain ⟨r₂, hr₂, hAB⟩ := Metric.eventually_nhds_iff.mp
    (hAa.eventually_analyticAt.and hBa.eventually_analyticAt)
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hA : ∀ s : ℂ, ‖s‖ < r → AnalyticAt ℂ A s := by
    intro s hs
    have hs' : dist s 0 < r₂ := by
      simpa only [dist_zero_right] using hs.trans_le (min_le_right r₁ r₂)
    exact (hAB hs').1
  have hB : ∀ s : ℂ, ‖s‖ < r → AnalyticAt ℂ B s := by
    intro s hs
    have hs' : dist s 0 < r₂ := by
      simpa only [dist_zero_right] using hs.trans_le (min_le_right r₁ r₂)
    exact (hAB hs').2
  let MΓ : ℝ := ‖Γ 0‖ + 1
  have hMΓ : 0 ≤ MΓ := by dsimp [MΓ]; positivity
  have hΓbound : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), ‖Γ p‖ < MΓ :=
    hΓa.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [MΓ]; linarith))
  obtain ⟨η, hη, hΓdata⟩ := Metric.eventually_nhds_iff.mp
    (hΓa.eventually_analyticAt.and hΓbound)
  have hΓ : ∀ p : ℂ × ℂ, ‖p‖ < η → AnalyticAt ℂ Γ p := by
    intro p hp
    exact (hΓdata (by simpa [dist_zero_right] using hp)).1
  have hΓnorm : ∀ p : ℂ × ℂ, ‖p‖ < η → ‖Γ p‖ ≤ MΓ := by
    intro p hp
    exact (hΓdata (by simpa [dist_zero_right] using hp)).2.le
  refine ⟨max 64 (4 / η), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro R hR Z hZ u hu hZu
  have hR64 : 64 ≤ R := (le_max_left _ _).trans hR
  have hRη : 4 / η ≤ R := (le_max_right _ _).trans hR
  let c : ℝ := min (parameterRadius Z 0 / 2) (min (η ^ 2 / 4) (r / 2))
  have hc : 0 < c := lt_min (div_pos (parameterRadius_pos Z hZ 0) (by norm_num))
    (lt_min (by positivity) (by positivity))
  have hcZ : c < parameterRadius Z 0 := lt_of_le_of_lt (min_le_left _ _)
    (by linarith [parameterRadius_pos Z hZ 0])
  have hcη : c ≤ η ^ 2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcr : c < r := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  refine ⟨c, MΓ * (16 + Cq * c) ^ N, hc, by positivity, ?_, ?_⟩
  · exact diffContOnCl_descendedTerm A B Γ N u R Z η r c hR64 hu hZu hη hRη
      hc hcZ hcη hcr hA hB hΓ hEven
  · intro k z hz
    exact norm_descendedTerm_le A B Γ N u z R Z η r c Cq MΓ hR64 hu hZu hη hRη
      hc hcZ hcη hcr hCq hMΓ
      (fun s v hs hv => hqbound s v (hs.trans_le (min_le_left _ _)) hv)
      hΓnorm k hz

/-- The disc radius and residual constant are chosen before the initial
point, giving common complex-parameter estimates on every bounded petal set. -/
theorem exists_uniform_prepared_orbit_disc_bounds
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (hAa : AnalyticAt ℂ A 0) (hBa : AnalyticAt ℂ B 0)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0) (hΓa : AnalyticAt ℂ Γ 0)
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ Z : ℝ, 0 ≤ Z →
      ∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧
        ∀ u : ℂ, R ≤ (inverseCoordinate u).re → ‖inverseCoordinate u‖ ≤ Z →
          (∀ k, DiffContOnCl ℂ (fun z => descendedTerm A B Γ N u z k)
            (ball 0 (c / ((k : ℝ) + 1) ^ 2))) ∧
          (∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
            ‖descendedTerm A B Γ N u z k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) := by
  obtain ⟨r₁, Cq, hr₁, hCq, hqbound⟩ :=
    AnalyticRootBounds.rootPolynomial_norm_bound hAa hBa hA0 hB0
  obtain ⟨r₂, hr₂, hAB⟩ := Metric.eventually_nhds_iff.mp
    (hAa.eventually_analyticAt.and hBa.eventually_analyticAt)
  let r : ℝ := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hA : ∀ s : ℂ, ‖s‖ < r → AnalyticAt ℂ A s := by
    intro s hs
    have hs' : dist s 0 < r₂ := by
      simpa only [dist_zero_right] using hs.trans_le (min_le_right r₁ r₂)
    exact (hAB hs').1
  have hB : ∀ s : ℂ, ‖s‖ < r → AnalyticAt ℂ B s := by
    intro s hs
    have hs' : dist s 0 < r₂ := by
      simpa only [dist_zero_right] using hs.trans_le (min_le_right r₁ r₂)
    exact (hAB hs').2
  let MΓ : ℝ := ‖Γ 0‖ + 1
  have hMΓ : 0 ≤ MΓ := by dsimp [MΓ]; positivity
  have hΓbound : ∀ᶠ p in 𝓝 (0 : ℂ × ℂ), ‖Γ p‖ < MΓ :=
    hΓa.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [MΓ]; linarith))
  obtain ⟨η, hη, hΓdata⟩ := Metric.eventually_nhds_iff.mp
    (hΓa.eventually_analyticAt.and hΓbound)
  have hΓ : ∀ p : ℂ × ℂ, ‖p‖ < η → AnalyticAt ℂ Γ p := by
    intro p hp
    exact (hΓdata (by simpa [dist_zero_right] using hp)).1
  have hΓnorm : ∀ p : ℂ × ℂ, ‖p‖ < η → ‖Γ p‖ ≤ MΓ := by
    intro p hp
    exact (hΓdata (by simpa [dist_zero_right] using hp)).2.le
  refine ⟨max 64 (4 / η), lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro R hR Z hZ
  have hR64 : 64 ≤ R := (le_max_left _ _).trans hR
  have hRη : 4 / η ≤ R := (le_max_right _ _).trans hR
  let c : ℝ := min (parameterRadius Z 0 / 2) (min (η ^ 2 / 4) (r / 2))
  have hc : 0 < c := lt_min (div_pos (parameterRadius_pos Z hZ 0) (by norm_num))
    (lt_min (by positivity) (by positivity))
  have hcZ : c < parameterRadius Z 0 := lt_of_le_of_lt (min_le_left _ _)
    (by linarith [parameterRadius_pos Z hZ 0])
  have hcη : c ≤ η ^ 2 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hcr : c < r := lt_of_le_of_lt
    ((min_le_right _ _).trans (min_le_right _ _)) (by linarith)
  refine ⟨c, MΓ * (16 + Cq * c) ^ N, hc, by positivity, ?_⟩
  intro u hu hZu
  constructor
  · exact diffContOnCl_descendedTerm A B Γ N u R Z η r c hR64 hu hZu hη hRη
      hc hcZ hcη hcr hA hB hΓ hEven
  · intro k z hz
    exact norm_descendedTerm_le A B Γ N u z R Z η r c Cq MΓ hR64 hu hZu hη hRη
      hc hcZ hcη hcr hCq hMΓ
      (fun s v hs hv => hqbound s v (hs.trans_le (min_le_left _ _)) hv)
      hΓnorm k hz

end Kneser.ReflectedEvenOrbitDiscs

end
