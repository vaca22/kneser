import Kneser.JointAnalyticFiniteTaylor

/-! Arbitrary finite integer expansions of genuine moving inverses.
The analytic reference inverse is constructed from the finite Taylor
family.  Stability then transfers its Cauchy remainder to the actual
inverse.  The final endpoint constructs every actual inverse branch too.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderMovingInverse

open Filter Set Metric
open scoped Topology
open Kneser.FiniteExpansionHolomorphy Kneser.StableHolomorphicInverse

theorem norm_inverse_fake_difference_le (F G : ℂ → ℂ) (V : ℂ → ℂ)
    (r ε : ℝ)
    (hF : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ) (ball (0 : ℂ) (2 * r)) (1 / 2))
    (z w : ℂ) (hV : V z ∈ ball (0 : ℂ) (2 * r)) (hw : w ∈ ball (0 : ℂ) (2 * r))
    (hVz : F (V z) = z) (hwz : G w = z) (herror : ‖F w - G w‖ ≤ ε) :
    ‖V z - w‖ ≤ 2 * ε := by
  have hh := norm_sub_le_two_mul_norm_image_sub F r hF (V z) w hV hw
  calc
    ‖V z - w‖ ≤ 2 * ‖F (V z) - F w‖ := hh
    _ = 2 * ‖F w - G w‖ := by
      rw [hVz, hwz]
      exact congrArg (fun x : ℝ => 2 * x) (norm_sub_rev z (F w))
    _ ≤ 2 * ε := mul_le_mul_of_nonneg_left herror (by norm_num)

/-- The local finite expansion is proved for any branch already obtained
by the stable inverse construction.  Inverse equations and geometry are
inputs to this transport lemma, not asymptotic expansion conclusions. -/
theorem local_finite_inverse_expansion (F V : ℝ → ℂ → ℂ)
    (c : ℕ → ℂ → ℂ) (m : ℕ) (r C : ℝ) (hr : 0 < r) (hC : 0 ≤ C)
    (hV0 : ∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z)
    (hV : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ ball (0 : ℂ) (r / 4),
      V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2))
    (hF : ∀ᶠ s : ℝ in 𝓝[>] 0, ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2))
    (ha0 : AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) (2 * r)))
    (hc : ∀ j ≤ m, AnalyticOnNhd ℂ (c j) (ball (0 : ℂ) (4 * r)))
    (hzero : ∀ u ∈ ball (0 : ℂ) (4 * r), c 0 u = F 0 u)
    (hExpansion : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s u - complexPolynomial c m (s : ℂ) u‖ ≤ C * s ^ (m + 1))
    (z₀ : ℂ) (hz₀ : z₀ ∈ ball (0 : ℂ) (r / 4)) :
    ∃ η : ℝ, 0 < η ∧ closedBall z₀ η ⊆ ball (0 : ℂ) (r / 4) ∧
      ∃ d : ℕ → ℂ → ℂ, ∃ D : ℝ, 0 ≤ D ∧
        (∀ j ≤ m, AnalyticOnNhd ℂ (d j) (ball z₀ η)) ∧
        (∀ z ∈ closedBall z₀ η, d 0 z = V 0 z) ∧
        (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall z₀ η,
          ‖V s z - complexPolynomial d m (s : ℂ) z‖ ≤ D * s ^ (m + 1)) := by
  have hsub : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) (2 * r) := by
    intro u hu
    simp only [mem_ball, dist_zero_right]
    have hn : ‖u‖ ≤ r := by simpa only [mem_closedBall, dist_zero_right] using hu
    linarith
  have hsub4 : ball (0 : ℂ) (2 * r) ⊆ ball (0 : ℂ) (4 * r) := by
    intro u hu
    simp only [mem_ball, dist_zero_right] at hu ⊢
    linarith
  let v₀ := V 0 z₀
  have hv₀ : v₀ ∈ ball (0 : ℂ) (2 * r) := hsub (hV0 z₀ hz₀).1
  have hbase : c 0 v₀ = z₀ := (hzero v₀ (hsub4 hv₀)).trans (hV0 z₀ hz₀).2
  have hnearzero : c 0 =ᶠ[𝓝 v₀] F 0 := by
    filter_upwards [isOpen_ball.mem_nhds (hsub4 hv₀)] with u hu
    exact hzero u hu
  have hdne : deriv (c 0) v₀ ≠ 0 := by
    rw [hnearzero.deriv_eq]
    intro he
    have hh := norm_deriv_lower (F 0) r hF0 ha0 v₀ hv₀
    rw [he, norm_zero] at hh
    linarith
  obtain ⟨W, hWa, hWbase, hWeq⟩ := Kneser.FiniteTaylorImplicitInverse.exists_polynomial_implicit_inverse
    c m v₀ z₀ (fun j hj => hc j hj v₀ (hsub4 hv₀)) hbase hdne
  have hWsource : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, z₀), W p ∈ ball (0 : ℂ) (2 * r) := by
    have hb : W (0, z₀) ∈ ball (0 : ℂ) (2 * r) := by rwa [hWbase]
    exact hWa.continuousAt.eventually (isOpen_ball.mem_nhds hb)
  have hzsource : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, z₀), p.2 ∈ ball (0 : ℂ) (r / 4) :=
    continuous_snd.continuousAt.eventually (isOpen_ball.mem_nhds hz₀)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp (hWeq.and (hWsource.and hzsource))
  obtain ⟨R, hR, CW, hCW, hdanalytic, hWTaylor⟩ :=
    Kneser.JointAnalyticFiniteTaylor.exists_uniform_finite_taylor W z₀ hWa m
  let η := min (R / 2) (δ / 4)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηR : η ≤ R := (min_le_left _ _).trans (by linarith)
  have hηδ : η < δ := (min_le_right _ _).trans_lt (by linarith)
  have hpoint (s : ℂ) (hs : ‖s‖ ≤ δ / 4) (z : ℂ) (hz : z ∈ closedBall z₀ η) :
      complexPolynomial c m s (W (s, z)) = z ∧
        W (s, z) ∈ ball (0 : ℂ) (2 * r) ∧ z ∈ ball (0 : ℂ) (r / 4) := by
    apply hδbound (y := (s, z))
    rw [Prod.dist_eq]
    apply max_lt_iff.mpr
    exact ⟨(by simpa only [dist_zero_right] using hs.trans_lt (by linarith : δ / 4 < δ)),
      (show dist z z₀ ≤ η from hz).trans_lt hηδ⟩
  have hclosedImage : closedBall z₀ η ⊆ ball (0 : ℂ) (r / 4) :=
    fun z hz => (hpoint 0 (by simp; positivity) z hz).2.2
  let d := Kneser.JointAnalyticFiniteTaylor.coefficient W
  have hd0 (z : ℂ) (hz : z ∈ closedBall z₀ η) : d 0 z = V 0 z := by
    rw [show d 0 z = W (0, z) from Kneser.JointAnalyticFiniteTaylor.coefficient_zero W z]
    have hw := hpoint 0 (by simp; positivity) z hz
    have hW0 : F 0 (W (0, z)) = z := by
      rw [Kneser.FiniteTaylorImplicitInverse.complexPolynomial_zero,
        hzero _ (hsub4 hw.2.1)] at hw
      exact hw.1
    have hv := hV0 z (hclosedImage hz)
    have hn := norm_sub_le_two_mul_norm_image_sub (F 0) r hF0
      (W (0, z)) (V 0 z) hw.2.1 (hsub hv.1)
    rw [hW0, hv.2, sub_self, norm_zero, mul_zero] at hn
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))
  refine ⟨η, hη, hclosedImage, d, 2 * C + CW, by positivity, ?_, hd0, ?_⟩
  · intro j hj
    exact (hdanalytic j hj).mono (by
      intro z hz
      exact (ball_subset_ball hηR) hz)
  · have hsδ : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ δ / 4 :=
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < δ / 4)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    have hsR : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ R / 2 :=
      ((eventually_lt_nhds (by positivity : (0 : ℝ) < R / 2)).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
    filter_upwards [hV, hF, hExpansion, hsδ, hsR, self_mem_nhdsWithin] with s hv hf he hsδ hsR hsp
    change 0 < s at hsp
    have hnorm : ‖(s : ℂ)‖ = s := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
    intro z hz
    have hw := hpoint (s : ℂ) (by rwa [hnorm]) z hz
    have hvz := hv z (hclosedImage hz)
    have hwe : W ((s : ℂ), z) ∈ closedBall (0 : ℂ) (4 * r) := by
      have hww := hw.2.1
      simp only [mem_ball, mem_closedBall, dist_zero_right] at hww ⊢
      linarith
    have hdiff := norm_inverse_fake_difference_le (F s) (complexPolynomial c m (s : ℂ)) (V s)
      r (C * s ^ (m + 1)) hf z (W ((s : ℂ), z)) (hsub hvz.1) hw.2.1 hvz.2 hw.1 (he _ hwe)
    have ht := hWTaylor (s : ℂ) (by rwa [hnorm]) z ((closedBall_subset_closedBall hηR) hz)
    rw [hnorm] at ht
    have heq : V s z - complexPolynomial d m (s : ℂ) z =
        (V s z - W ((s : ℂ), z)) +
          (W ((s : ℂ), z) - complexPolynomial d m (s : ℂ) z) := by ring
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add hdiff ht).trans_eq (by ring))

/-- Every branch used in the finite expansion is constructed from the
actual holomorphic family.  No moving inverse or inverse asymptotics are
hypotheses of this endpoint. -/
theorem exists_finite_inverse_expansion (F : ℝ → ℂ → ℂ)
    (c : ℕ → ℂ → ℂ) (m : ℕ) (r C : ℝ) (ε : ℝ → ℝ)
    (hr : 0 < r) (hC : 0 ≤ C) (h00 : F 0 0 = 0)
    (hF0 : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 4))
    (ha0 : DiffContOnCl ℂ (F 0) (ball (0 : ℂ) (4 * r)))
    (ha : ∀ᶠ s : ℝ in 𝓝[>] 0, DiffContOnCl ℂ (F s) (ball (0 : ℂ) (4 * r)))
    (hε : Tendsto ε (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s u - F 0 u‖ ≤ ε s)
    (hc : ∀ j ≤ m, AnalyticOnNhd ℂ (c j) (ball (0 : ℂ) (4 * r)))
    (hzero : ∀ u ∈ ball (0 : ℂ) (4 * r), c 0 u = F 0 u)
    (hExpansion : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ closedBall (0 : ℂ) (4 * r),
      ‖F s u - complexPolynomial c m (s : ℂ) u‖ ≤ C * s ^ (m + 1)) :
    ∃ V : ℝ → ℂ → ℂ,
      (∀ z ∈ ball (0 : ℂ) (r / 4), V 0 z ∈ closedBall (0 : ℂ) r ∧ F 0 (V 0 z) = z) ∧
      AnalyticOnNhd ℂ (V 0) (ball (0 : ℂ) (r / 4)) ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ z ∈ ball (0 : ℂ) (r / 4), V s z ∈ closedBall (0 : ℂ) r ∧ F s (V s z) = z) ∧
        AnalyticOnNhd ℂ (V s) (ball (0 : ℂ) (r / 4))) ∧
      (∀ z₀ ∈ ball (0 : ℂ) (r / 4),
        ∃ η : ℝ, 0 < η ∧ closedBall z₀ η ⊆ ball (0 : ℂ) (r / 4) ∧
          ∃ d : ℕ → ℂ → ℂ, ∃ D : ℝ, 0 ≤ D ∧
            (∀ j ≤ m, AnalyticOnNhd ℂ (d j) (ball z₀ η)) ∧
            (∀ z ∈ closedBall z₀ η, d 0 z = V 0 z) ∧
            (∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ closedBall z₀ η,
              ‖V s z - complexPolynomial d m (s : ℂ) z‖ ≤ D * s ^ (m + 1))) := by
  obtain ⟨V, hV0, hVa0, hV, _⟩ := exists_stable_inverse_family F r ε hr h00 hF0 ha0 ha hε hbound
  have hhalf : ApproximatesLinearOn (F 0) (ContinuousLinearMap.id ℂ ℂ)
      (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    intro x hx y hy
    exact (hF0 x hx y hy).trans (by norm_num; nlinarith [norm_nonneg (x-y)])
  have ha0' : AnalyticOnNhd ℂ (F 0) (ball (0 : ℂ) (2 * r)) := by
    intro u hu
    apply ha0.differentiableOn.analyticAt
    apply isOpen_ball.mem_nhds
    simp only [mem_ball, dist_zero_right] at hu ⊢
    linarith
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, ε s ≤ r / 4 :=
    (hε.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < r / 4))).mono fun _ h => h.le
  have hhalfMoving : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ApproximatesLinearOn (F s) (ContinuousLinearMap.id ℂ ℂ) (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    filter_upwards [ha, hbound, hsmall] with s hs hb hεs
    exact approximates_identity_of_disc_error (F 0) (F s) r (ε s) hr hF0
      (by convert hs.sub ha0 using 1; rfl) hb hεs
  refine ⟨V, hV0, hVa0, hV.mono (fun _ hs => ⟨hs.1, hs.2.1⟩), ?_⟩
  intro z₀ hz₀
  exact local_finite_inverse_expansion F V c m r C hr hC hV0 (hV.mono (fun _ hs => hs.1))
    hhalf hhalfMoving ha0' hc hzero hExpansion z₀ hz₀

end Kneser.AllOrderMovingInverse

end
