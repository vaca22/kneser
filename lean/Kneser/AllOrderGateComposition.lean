import Kneser.FiniteLocalExpansionGluing
import Kneser.QuantitativeGateTransition

/-! True finite-order moving composition estimates.  Coefficient bounds
and spatial Lipschitz constants are derived from holomorphy on compact
discs.  A finite polynomial reference composition is jointly analytic;
its Cauchy remainder transfers to the actual moving composition. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderGateComposition

open Filter Set Metric
open scoped Topology BigOperators
open Kneser.FiniteExpansionHolomorphy Kneser.StableHolomorphicInverse

theorem exists_finite_coefficient_bound (a : ℕ → ℂ → ℂ) (m : ℕ) (K : Set ℂ)
    (hK : IsCompact K) (ha : ∀ j ≤ m, AnalyticOnNhd ℂ (a j) K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j ≤ m, ∀ u ∈ K, ‖a j u‖ ≤ M := by
  have hh (i : Fin (m + 1)) := hK.exists_bound_of_continuousOn
    (ha i (by omega)).continuousOn
  choose B hB using hh
  let M := ∑ i : Fin (m + 1), max (B i) 0
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro j hj u hu
  let i : Fin (m + 1) := ⟨j, by omega⟩
  exact (hB i u hu).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun k _ => le_max_right (B k) 0) (Finset.mem_univ i)))

theorem polynomial_diffContOnCl (a : ℕ → ℂ → ℂ) (m : ℕ) (s : ℂ) (r : ℝ)
    (ha : ∀ j ≤ m, AnalyticOnNhd ℂ (a j) (closedBall (0 : ℂ) (4 * r))) :
    DiffContOnCl ℂ (complexPolynomial a m s) (ball (0 : ℂ) (4 * r)) := by
  apply DifferentiableOn.diffContOnCl
  intro u hu
  have huu := closure_ball_subset_closedBall hu
  have hh := analyticAt_complexPolynomial a m s u (fun j hj => ha j hj u huu)
  exact (hh.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl).differentiableAt.differentiableWithinAt

theorem norm_polynomial_le (a : ℕ → ℂ → ℂ) (m : ℕ) (M s : ℝ)
    (hM : 0 ≤ M) (hs : 0 ≤ s) (hs1 : s ≤ 1) (u : ℂ)
    (hb : ∀ j ≤ m, ‖a j u‖ ≤ M) :
    ‖complexPolynomial a m (s : ℂ) u‖ ≤ ((m + 1 : ℕ) : ℝ) * M := by
  unfold complexPolynomial
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), M := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
      exact (mul_le_mul (pow_le_one₀ hs hs1) (hb j (by have h := Finset.mem_range.mp hj; omega))
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul M)
    _ = _ := by simp

theorem exists_uniform_polynomial_lipschitz (a : ℕ → ℂ → ℂ) (m : ℕ) (r : ℝ)
    (hr : 0 < r)
    (ha : ∀ j ≤ m, AnalyticOnNhd ℂ (a j) (closedBall (0 : ℂ) (4 * r))) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ u ∈ ball (0 : ℂ) (2 * r), ∀ v ∈ ball (0 : ℂ) (2 * r),
        ‖complexPolynomial a m (s : ℂ) u - complexPolynomial a m (s : ℂ) v‖ ≤ L * ‖u - v‖ := by
  obtain ⟨M, hM, hb⟩ := exists_finite_coefficient_bound a m (closedBall (0 : ℂ) (4 * r))
    (isCompact_closedBall _ _) ha
  let B := ((m + 1 : ℕ) : ℝ) * M
  refine ⟨B / r, by dsimp [B]; positivity, ?_⟩
  intro s hs hs1 u hu v hv
  have hpoly := polynomial_diffContOnCl a m (s : ℂ) r ha
  have hbound : ∀ w ∈ closedBall (0 : ℂ) (4 * r), ‖complexPolynomial a m (s : ℂ) w‖ ≤ B :=
    fun w hw => norm_polynomial_le a m M s hM hs hs1 w (fun j hj => hb j hj w hw)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ)
    (s := ball (0 : ℂ) (2 * r))
    (fun w hw => hpoly.differentiableAt isOpen_ball (by
      simp only [mem_ball, dist_zero_right] at hw ⊢; linarith))
    (fun w hw => norm_deriv_le_of_disc_bound _ r B hr hpoly hbound w hw)
    (convex_ball (0 : ℂ) (2 * r)) hv hu

/-- The inverse expansion is already a proved result of
AllOrderMovingInverse.  This transport lemma proves the composition
remainder from it and from the actual coordinate expansion. -/
theorem local_finite_composition_expansion (A V : ℝ → ℂ → ℂ)
    (a d : ℕ → ℂ → ℂ) (m : ℕ) (r η CA CV : ℝ) (z₀ : ℂ)
    (hr : 0 < r) (hη : 0 < η) (hCA : 0 ≤ CA) (hCV : 0 ≤ CV)
    (ha : ∀ j ≤ m, AnalyticOnNhd ℂ (a j) (closedBall (0 : ℂ) (4 * r)))
    (hd : ∀ j ≤ m, AnalyticOnNhd ℂ (d j) (ball z₀ η))
    (ha0 : ∀ u ∈ ball (0 : ℂ) (4 * r), a 0 u = A 0 u)
    (hd0 : ∀ z ∈ closedBall z₀ η, d 0 z = V 0 z)
    (hV0 : ∀ z ∈ closedBall z₀ η, V 0 z ∈ closedBall (0 : ℂ) r)
    (hV : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall z₀ η, V s z ∈ closedBall (0 : ℂ) r)
    (hA : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖A s u - complexPolynomial a m (s : ℂ) u‖ ≤ CA * s ^ (m + 1))
    (hInverse : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall z₀ η,
      ‖V s z - complexPolynomial d m (s : ℂ) z‖ ≤ CV * s ^ (m + 1)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ η ∧ ∃ b : ℕ → ℂ → ℂ, ∃ C : ℝ, 0 ≤ C ∧
      (∀ j ≤ m, AnalyticOnNhd ℂ (b j) (ball z₀ ρ)) ∧
      (∀ z ∈ closedBall z₀ ρ, b 0 z = A 0 (V 0 z)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall z₀ ρ,
        ‖A s (V s z) - complexPolynomial b m (s : ℂ) z‖ ≤ C * s ^ (m + 1)) := by
  let G : ℂ × ℂ → ℂ := fun p => complexPolynomial d m p.1 p.2
  let J : ℂ × ℂ → ℂ := fun p => complexPolynomial a m p.1 (G p)
  have hG : AnalyticAt ℂ G (0, z₀) := analyticAt_complexPolynomial d m 0 z₀
    (fun j hj => hd j hj z₀ (mem_ball_self hη))
  have hGbase : G (0, z₀) = V 0 z₀ := by
    change complexPolynomial d m 0 z₀ = V 0 z₀
    rw [Kneser.FiniteTaylorImplicitInverse.complexPolynomial_zero]
    exact hd0 z₀ (mem_closedBall_self hη.le)
  have hv₀ : V 0 z₀ ∈ ball (0 : ℂ) (2 * r) := by
    have hn := hV0 z₀ (mem_closedBall_self hη.le)
    simp only [mem_closedBall, mem_ball, dist_zero_right] at hn ⊢
    linarith
  have hJ : AnalyticAt ℂ J (0, z₀) := by
    have houter := analyticAt_complexPolynomial a m 0 (V 0 z₀) (fun j hj => ha j hj _
      (by have hn := hv₀; simp only [mem_ball, mem_closedBall, dist_zero_right] at hn ⊢; linarith))
    exact houter.comp_of_eq (analyticAt_fst.prod hG) (by simp only [hGbase])
  have hsource : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, z₀), G p ∈ ball (0 : ℂ) (2 * r) := by
    have hbase : G (0, z₀) ∈ ball (0 : ℂ) (2 * r) := by rwa [hGbase]
    exact hG.continuousAt.eventually (isOpen_ball.mem_nhds hbase)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hsource
  obtain ⟨R, hR, CJ, hCJ, hbj, hJTaylor⟩ :=
    Kneser.JointAnalyticFiniteTaylor.exists_uniform_finite_taylor J z₀ hJ m
  obtain ⟨L, hL, hLip⟩ := exists_uniform_polynomial_lipschitz a m r hr ha
  let ρ := min (η / 2) (min (R / 2) (δ / 4))
  have hρ : 0 < ρ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hρη : ρ ≤ η := (min_le_left _ _).trans (by linarith)
  have hρR : ρ ≤ R := ((min_le_right _ _).trans (min_le_left _ _)).trans (by linarith)
  have hρδ : ρ < δ := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (by linarith)
  have hpoint (s : ℂ) (hs : ‖s‖ ≤ δ / 4) (z : ℂ) (hz : z ∈ closedBall z₀ ρ) :
      G (s, z) ∈ ball (0 : ℂ) (2 * r) := by
    apply hδbound (y := (s, z))
    rw [Prod.dist_eq]
    exact max_lt_iff.mpr ⟨(by simpa only [dist_zero_right] using hs.trans_lt (by linarith : δ / 4 < δ)),
      (show dist z z₀ ≤ ρ from hz).trans_lt hρδ⟩
  let b := Kneser.JointAnalyticFiniteTaylor.coefficient J
  refine ⟨ρ, hρ, hρη, b, CA + L * CV + CJ, by positivity, ?_, ?_, ?_⟩
  · intro j hj
    exact (hbj j hj).mono (ball_subset_ball hρR)
  · intro z hz
    rw [show b 0 z = J (0, z) from Kneser.JointAnalyticFiniteTaylor.coefficient_zero J z]
    change complexPolynomial a m 0 (complexPolynomial d m 0 z) = A 0 (V 0 z)
    rw [Kneser.FiniteTaylorImplicitInverse.complexPolynomial_zero,
      Kneser.FiniteTaylorImplicitInverse.complexPolynomial_zero, hd0 z ((closedBall_subset_closedBall hρη) hz)]
    apply ha0
    have hn := hV0 z ((closedBall_subset_closedBall hρη) hz)
    simp only [mem_closedBall, mem_ball, dist_zero_right] at hn ⊢
    linarith
  · have hsδ : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ δ / 4 :=
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < δ / 4)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    have hsR : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ R / 2 :=
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < R / 2)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    have hs1 : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
      ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    filter_upwards [hA, hInverse, hV, hsδ, hsR, hs1, self_mem_nhdsWithin] with s haS hvS hvs hsδ hsR hs1 hsp
    change 0 < s at hsp
    have hnorm : ‖(s : ℂ)‖ = s := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
    intro z hz
    have hzin := (closedBall_subset_closedBall hρη) hz
    have htrue := hvs z hzin
    have htrue2 : V s z ∈ ball (0 : ℂ) (2 * r) := by
      simp only [mem_closedBall, mem_ball, dist_zero_right] at htrue ⊢; linarith
    have htrue4 : V s z ∈ closedBall (0 : ℂ) (4 * r) := by
      simp only [mem_closedBall, dist_zero_right] at htrue ⊢; linarith
    have hfake := hpoint (s : ℂ) (by rwa [hnorm]) z hz
    have hspatial := hLip s hsp.le hs1 _ htrue2 _ hfake
    have hVerror := hvS z hzin
    have hcomp : ‖complexPolynomial a m (s : ℂ) (V s z) - J ((s : ℂ), z)‖ ≤
        L * CV * s ^ (m + 1) :=
      hspatial.trans ((mul_le_mul_of_nonneg_left hVerror hL).trans_eq (by ring))
    have hTaylor := hJTaylor (s : ℂ) (by rwa [hnorm]) z ((closedBall_subset_closedBall hρR) hz)
    rw [hnorm] at hTaylor
    have he : A s (V s z) - complexPolynomial b m (s : ℂ) z =
        (A s (V s z) - complexPolynomial a m (s : ℂ) (V s z)) +
        (complexPolynomial a m (s : ℂ) (V s z) - J ((s : ℂ), z)) +
        (J ((s : ℂ), z) - complexPolynomial b m (s : ℂ) z) := by ring
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl) |>.trans
      ((add_le_add (add_le_add (haS _ htrue4) hcomp) hTaylor).trans_eq (by ring))

end Kneser.AllOrderGateComposition

end
