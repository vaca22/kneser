import Kneser.HigherMovingSeed
import Kneser.ParabolicOverlapGate
import Kneser.ParabolicFatouHolomorphic

/-! Genuine shrinking parameter discs for an actual orbit whose initial
point varies analytically with the parameter. The moving initial point is
controlled on one compact complex-parameter image; holomorphy of the whole
composed orbit term is proved, rather than inferred from separate slices. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Kneser.HigherMovingOrbitDiscs

open Filter Set Metric Kneser.ExponentialUnfolding Kneser.ParabolicExponentialOrbit
open Kneser.ExponentialRootPolynomial Kneser.EvenPreparedOrbitDiscs
open Kneser.HigherMovingSeed Kneser.PerturbedExponentialOrbit
open scoped Topology

def splitTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (W : ℂ × ℂ → ℂ) (u x : ℂ) (k : ℕ) : ℂ :=
  rootPolynomial A B (x ^ 2) (orbit (W (x ^ 2, u)) (x ^ 2) k) ^ N *
    Γ (x, orbit (W (x ^ 2, u)) (x ^ 2) k)

def descendedTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (W : ℂ × ℂ → ℂ) (u s : ℂ) (k : ℕ) : ℂ :=
  splitTerm A B Γ N W u (Complex.sqrt s) k

theorem descendedTerm_eq (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (W : ℂ × ℂ → ℂ) (u s : ℂ) (k : ℕ) :
    descendedTerm A B Γ N W u s k =
      EvenPreparedOrbitDiscs.descendedTerm A B Γ N (W (s, u)) s k := by
  simp only [descendedTerm, splitTerm, EvenPreparedOrbitDiscs.descendedTerm,
    EvenPreparedOrbitDiscs.splitTerm, AnalyticEvenDescent.square_sqrt]

theorem even_splitTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (W : ℂ × ℂ → ℂ) (u : ℂ) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) (k : ℕ) (x : ℂ) :
    splitTerm A B Γ N W u (-x) k = splitTerm A B Γ N W u x k := by
  simp only [splitTerm, neg_sq, hEven]

theorem analyticAt_descendedTerm (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (W : ℂ × ℂ → ℂ) (u s : ℂ) (k : ℕ)
    (hW : AnalyticAt ℂ W (s, u)) (hA : AnalyticAt ℂ A s) (hB : AnalyticAt ℂ B s)
    (hΓ : AnalyticAt ℂ Γ (Complex.sqrt s, orbit (W (s, u)) s k))
    (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    AnalyticAt ℂ (fun z => descendedTerm A B Γ N W u z k) s := by
  let x := Complex.sqrt s
  have hs : AnalyticAt ℂ (fun y : ℂ => y ^ 2) x := analyticAt_id.pow 2
  have hw : AnalyticAt ℂ (fun y => W (y ^ 2, u)) x :=
    hW.comp_of_eq (hs.prod analyticAt_const) (by simp [x])
  have ho : AnalyticAt ℂ (fun y => orbit (W (y ^ 2, u)) (y ^ 2) k) x :=
    (ParabolicOverlapGate.analyticAt_forward_orbit_joint (W (s, u)) s k).comp_of_eq
      (hs.prod hw) (by simp [x])
  have hsplit : AnalyticAt ℂ (fun y => splitTerm A B Γ N W u y k) x := by
    apply (((ho.pow 2).sub ((hA.comp_of_eq hs (by simp [x])).mul ho)).add
      (hB.comp_of_eq hs (by simp [x]))).pow N |>.mul
      (hΓ.comp_of_eq (analyticAt_id.prod ho) (by simp [x]))
  by_cases hz : s = 0
  · subst s
    exact AnalyticEvenDescent.analyticAt_even_sqrt
      (even_splitTerm A B Γ N W u hEven k) (by simpa [x] using hsplit)
  · exact AnalyticEvenDescent.analyticAt_even_sqrt_of_ne
      (even_splitTerm A B Γ N W u hEven k) hz hsplit

theorem exists_moving_orbit_disc_bounds
    (A B : ℂ → ℂ) (Γ : ℂ × ℂ → ℂ) (N : ℕ)
    (hA : AnalyticAt ℂ A 0) (hB : AnalyticAt ℂ B 0) (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hΓ : AnalyticAt ℂ Γ 0) (hEven : ∀ x v, Γ (-x, v) = Γ (x, v)) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ W : ℂ × ℂ → ℂ, ∀ S : Set ℂ, IsCompact S →
      (∀ u ∈ S, AnalyticAt ℂ W (0, u)) →
      (∀ u ∈ S, R₀ + 2 ≤ (inverseCoordinate (W (0, u))).re) →
        ∃ c M : ℝ, 0 < c ∧ 0 ≤ M ∧
          (∀ u ∈ S, ∀ k, DiffContOnCl ℂ (fun z => descendedTerm A B Γ N W u z k)
            (ball 0 (c / ((k : ℝ) + 1) ^ 2))) ∧
          (∀ u ∈ S, ∀ (k : ℕ) (z : ℂ), ‖z‖ ≤ c / ((k : ℝ) + 1) ^ 2 →
            ‖descendedTerm A B Γ N W u z k‖ ≤ M / ((k : ℝ) + 1) ^ (2 * N)) := by
  obtain ⟨R₁, hR₁, hdiscs⟩ := EvenPreparedOrbitDiscs.exists_uniform_prepared_orbit_disc_bounds
    A B Γ N hA hB hA0 hB0 hΓ hEven
  obtain ⟨r, hr, hAB⟩ := Metric.eventually_nhds_iff.mp
    (hA.eventually_analyticAt.and hB.eventually_analyticAt)
  obtain ⟨η, hη, hΓnear⟩ := Metric.eventually_nhds_iff.mp hΓ.eventually_analyticAt
  let R₀ : ℝ := max R₁ (max 64 (4 / η))
  have hR₀ : 0 < R₀ := hR₁.trans_le (le_max_left _ _)
  have hR64 : 64 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hRη : 4 / η ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨R₀, hR₀, ?_⟩
  intro W S hS hW hdeep
  obtain ⟨rW, K, hrW, hK, hKV, hWK⟩ := exists_compact_complex_image_neighborhood
    W S (ParabolicFatouHolomorphic.petal (R₀ + 1)) hS
      (ParabolicFatouHolomorphic.petal_isOpen (by positivity)) hW
      (fun u hu => by change R₀ + 1 < _; linarith [hdeep u hu])
  have hne : ∀ v ∈ K, v ≠ 0 := by
    intro v hv heq
    have hh := hKV hv
    change R₀ + 1 < (inverseCoordinate v).re at hh
    simp only [heq, inverseCoordinate, div_zero, Complex.zero_re] at hh
    linarith
  have hi : ContinuousOn inverseCoordinate K := by
    intro v hv; exact (continuousAt_const.div continuousAt_id (hne v hv)).continuousWithinAt
  obtain ⟨Z₁, hZ₁⟩ := hK.exists_bound_of_continuousOn hi
  let Z : ℝ := max Z₁ 0
  have hZ : 0 ≤ Z := le_max_right _ _
  have hZK : ∀ v ∈ K, ‖inverseCoordinate v‖ ≤ Z :=
    fun v hv => (hZ₁ v hv).trans (le_max_left _ _)
  obtain ⟨c₁, M, hc₁, hM, hdisc⟩ := hdiscs R₀ (le_max_left _ _) Z hZ
  let c : ℝ := min c₁ (min rW (min (parameterRadius Z 0) (min (η ^ 2 / 4) (r / 2))))
  have hc : 0 < c := lt_min hc₁ (lt_min hrW (lt_min (parameterRadius_pos Z hZ 0)
    (lt_min (by positivity) (by positivity))))
  have hcc₁ : c ≤ c₁ := min_le_left _ _
  have hcW : c ≤ rW := (min_le_left _ _).trans' (min_le_right _ _)
  have hcZ : c ≤ parameterRadius Z 0 :=
    (min_le_left _ _).trans' ((min_le_right _ _).trans (min_le_right _ _))
  have hcη : c ≤ η ^ 2 / 4 := (min_le_left _ _).trans'
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcr : c < r := lt_of_le_of_lt ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) (by linarith)
  have hseed (u : ℂ) (hu : u ∈ S) (k : ℕ) (s : ℂ)
      (hs : ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2) :
      ‖s‖ ≤ c ∧ AnalyticAt ℂ W (s, u) ∧
        R₀ ≤ (inverseCoordinate (W (s, u))).re ∧ ‖inverseCoordinate (W (s, u))‖ ≤ Z := by
    have hsc : ‖s‖ ≤ c := hs.trans (div_le_self hc.le (by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]))
    obtain ⟨hwa, hwK⟩ := hWK s (by simpa [mem_closedBall, dist_zero_right] using hsc.trans hcW) u hu
    have hd := hKV hwK
    change R₀ + 1 < _ at hd
    exact ⟨hsc, hwa, by linarith, hZK _ hwK⟩
  refine ⟨c, M, hc, hM, ?_, ?_⟩
  · intro u hu k
    have hd : DifferentiableOn ℂ (fun z => descendedTerm A B Γ N W u z k)
        (closedBall 0 (c / ((k : ℝ) + 1) ^ 2)) := by
      intro s hs
      have hsn : ‖s‖ ≤ c / ((k : ℝ) + 1) ^ 2 := by simpa [mem_closedBall, dist_zero_right] using hs
      obtain ⟨hsc, hwa, hdeep', hZ'⟩ := hseed u hu k s hsn
      have hAB' := hAB (by simpa [dist_zero_right] using hsc.trans_lt hcr)
      have hg : AnalyticAt ℂ Γ (Complex.sqrt s, orbit (W (s, u)) s k) :=
        hΓnear (by simpa only [dist_zero_right] using
          finite_orbit_graph_small (W (s, u)) s R₀ Z η c k hR64 hdeep' hZ' hη hRη hcZ hcη hsn)
      exact (analyticAt_descendedTerm A B Γ N W u s k hwa hAB'.1 hAB'.2 hg hEven).differentiableAt.differentiableWithinAt
    exact (hd.mono closure_ball_subset_closedBall).diffContOnCl
  · intro u hu k s hs
    obtain ⟨_, _, hdeep', hZ'⟩ := hseed u hu k s hs
    rw [descendedTerm_eq]
    exact (hdisc _ hdeep' hZ').2 k s
      (hs.trans (div_le_div_of_nonneg_right hcc₁ (by positivity)))

end Kneser.HigherMovingOrbitDiscs

end
