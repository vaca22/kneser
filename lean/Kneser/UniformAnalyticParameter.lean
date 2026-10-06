import Kneser.UniformModelTime

/-!
Joint analytic germs have common parameter discs, Taylor bounds and
linear increment bounds over each compact spatial set.
-/

noncomputable section

namespace Kneser.UniformAnalyticParameter

open Set Filter Metric
open scoped Topology

theorem exists_uniform_disc_bounds (Q : ℂ × ℂ → ℂ) (u₀ : ℂ)
    (hQ : AnalyticAt ℂ Q (0, u₀)) :
    ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧ ∀ u ∈ ball u₀ ρ,
      DiffContOnCl ℂ (fun s => Q (s, u)) (ball 0 r) ∧
        ∀ s ∈ closedBall (0 : ℂ) r, ‖Q (s, u)‖ ≤ M := by
  let B : ℂ × ℂ → ℂ := fun p => Q (p.1 ^ 2, p.2)
  have hB : AnalyticAt ℂ B (0, u₀) :=
    hQ.comp_of_eq (f := fun p : ℂ × ℂ => (p.1 ^ 2, p.2))
      ((analyticAt_fst.pow 2).prod analyticAt_snd) (by simp)
  have hEven : ∀ x u, B (-x, u) = B (x, u) := by intro x u; simp [B]
  obtain ⟨r, ρ, M, hr, hρ, hM, hlocal⟩ :=
    UniformModelTime.exists_uniform_even_disc_bounds u₀ hB hEven
  refine ⟨r, ρ, M, hr, hρ, hM, ?_⟩
  simpa only [B, AnalyticEvenDescent.square_sqrt] using hlocal

theorem exists_compact_disc_bounds (Q : ℂ × ℂ → ℂ) (S : Set ℂ)
    (hS : IsCompact S) (hQ : ∀ u ∈ S, AnalyticAt ℂ Q (0, u)) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ u ∈ S,
      DiffContOnCl ℂ (fun s => Q (s, u)) (ball 0 r) ∧
        ∀ s ∈ closedBall (0 : ℂ) r, ‖Q (s, u)‖ ≤ M := by
  classical
  rcases S.eq_empty_or_nonempty with hSE | hSN
  · subst S; exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
  have hloc : ∀ u : S, ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧
      ∀ v ∈ ball (u : ℂ) ρ,
        DiffContOnCl ℂ (fun s => Q (s, v)) (ball 0 r) ∧
          ∀ s ∈ closedBall (0 : ℂ) r, ‖Q (s, v)‖ ≤ M :=
    fun u => exists_uniform_disc_bounds Q u (hQ u u.property)
  choose r ρ M hr hρ hM hlocal using hloc
  have hcover : S ⊆ ⋃ u : S, ball (u : ℂ) (ρ u) := by
    intro u hu; exact mem_iUnion.mpr ⟨⟨u, hu⟩, mem_ball_self (hρ ⟨u, hu⟩)⟩
  obtain ⟨t, htcover⟩ := hS.elim_finite_subcover
    (fun u : S => ball (u : ℂ) (ρ u)) (fun _ => isOpen_ball) hcover
  have ht : t.Nonempty := by
    obtain ⟨u, hu⟩ := hSN
    obtain ⟨v, hv, _⟩ := mem_iUnion₂.mp (htcover hu)
    exact ⟨v, hv⟩
  let r₀ : ℝ := t.inf' ht r
  let M₀ : ℝ := t.sup' ht M
  have hr₀ : 0 < r₀ := (Finset.lt_inf'_iff ht).mpr (fun u _ => hr u)
  have hM₀ : 0 ≤ M₀ := by
    obtain ⟨u, hu⟩ := ht; exact (hM u).trans (Finset.le_sup' M hu)
  refine ⟨r₀, M₀, hr₀, hM₀, ?_⟩
  intro u hu
  obtain ⟨v, hv, huv⟩ := mem_iUnion₂.mp (htcover hu)
  have hrv : r₀ ≤ r v := Finset.inf'_le r hv
  refine ⟨(hlocal v u huv).1.mono (ball_subset_ball hrv), ?_⟩
  intro s hs
  exact ((hlocal v u huv).2 s (closedBall_subset_closedBall hrv hs)).trans (Finset.le_sup' M hv)

/-- The entire small-parameter image of a compact initial set lies in one
compact subset of the target open set. This is derived from joint germs. -/
theorem exists_compact_image_neighborhood (W : ℂ × ℂ → ℂ) (S V : Set ℂ)
    (hS : IsCompact S) (hV : IsOpen V)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u)) (hwV : ∀ u ∈ S, W (0, u) ∈ V) :
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ V ∧
      ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S, W (s, u) ∈ K := by
  have hnear : ∀ᶠ s : ℂ in 𝓝 0, ∀ u ∈ S,
      AnalyticAt ℂ W (s, u) ∧ W (s, u) ∈ V := by
    apply hS.eventually_forall_of_forall_eventually
    intro u hu
    exact (hW u hu).eventually_analyticAt.and
      ((hW u hu).continuousAt.eventually (hV.mem_nhds (hwV u hu)))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let T : Set (ℂ × ℂ) := closedBall (0 : ℂ) (r / 2) ×ˢ S
  have hT : IsCompact T := (isCompact_closedBall _ _).prod hS
  have hp : ∀ p ∈ T, AnalyticAt ℂ W p ∧ W p ∈ V := by
    intro p hp
    exact hball (by
      have hn : dist p.1 0 ≤ r / 2 := hp.1
      linarith) p.2 hp.2
  let K : Set ℂ := W '' T
  have hK : IsCompact K := hT.image_of_continuousOn
    (fun p hp' => (hp p hp').1.continuousAt.continuousWithinAt)
  refine ⟨K, hK, ?_, ?_⟩
  · rintro v ⟨p, hp', rfl⟩
    exact (hp p hp').2
  · have hs : ∀ᶠ s : ℝ in 𝓝[>] 0, (s : ℂ) ∈ closedBall (0 : ℂ) (r / 2) :=
      (Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually
        (closedBall_mem_nhds _ (by positivity : 0 < r / 2))
    filter_upwards [hs] with s hs u hu
    exact ⟨((s : ℂ), u), ⟨hs, hu⟩, rfl⟩

end Kneser.UniformAnalyticParameter

end
