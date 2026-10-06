import Kneser.ActualBilateralHigherPreparation
import Kneser.UniformAnalyticParameter

/-! Compact complex-parameter control of genuine moving initial points.
The source image and common model discs are derived from joint analytic
germs, before any orbit cutoff is chosen. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Kneser.HigherMovingSeed

open Filter Set Metric
open scoped Topology

theorem exists_compact_complex_image_neighborhood (W : ℂ × ℂ → ℂ) (S V : Set ℂ)
    (hS : IsCompact S) (hV : IsOpen V)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u)) (hwV : ∀ u ∈ S, W (0, u) ∈ V) :
    ∃ r : ℝ, ∃ K : Set ℂ, 0 < r ∧ IsCompact K ∧ K ⊆ V ∧
      ∀ z ∈ closedBall (0 : ℂ) r, ∀ u ∈ S,
        AnalyticAt ℂ W (z, u) ∧ W (z, u) ∈ K := by
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
    exact hball (by have hn : dist p.1 0 ≤ r / 2 := hp.1; linarith) p.2 hp.2
  let K : Set ℂ := W '' T
  have hK : IsCompact K := hT.image_of_continuousOn
    (fun p hp' => (hp p hp').1.continuousAt.continuousWithinAt)
  refine ⟨r / 2, K, by positivity, hK, ?_, ?_⟩
  · rintro v ⟨p, hp', rfl⟩
    exact (hp p hp').2
  · intro z hz u hu
    exact ⟨(hp (z, u) ⟨hz, hu⟩).1, ⟨(z, u), ⟨hz, hu⟩, rfl⟩⟩

theorem exists_compact_even_disc_bounds (Q : ℂ × ℂ → ℂ) (S : Set ℂ)
    (hS : IsCompact S) (hQ : ∀ u ∈ S, AnalyticAt ℂ Q (0, u))
    (hEven : ∀ x u, Q (-x, u) = Q (x, u)) :
    ∃ r M : ℝ, 0 < r ∧ 0 ≤ M ∧ ∀ u ∈ S,
      DiffContOnCl ℂ (fun s => Q (Complex.sqrt s, u)) (ball 0 r) ∧
        ∀ s ∈ closedBall (0 : ℂ) r, ‖Q (Complex.sqrt s, u)‖ ≤ M := by
  classical
  rcases S.eq_empty_or_nonempty with hSE | hSN
  · subst S; exact ⟨1, 0, by norm_num, by norm_num, by simp⟩
  have hloc : ∀ u : S, ∃ r ρ M : ℝ, 0 < r ∧ 0 < ρ ∧ 0 ≤ M ∧
      ∀ v ∈ ball (u : ℂ) ρ,
        DiffContOnCl ℂ (fun s => Q (Complex.sqrt s, v)) (ball 0 r) ∧
          ∀ s ∈ closedBall (0 : ℂ) r, ‖Q (Complex.sqrt s, v)‖ ≤ M :=
    fun u => UniformModelTime.exists_uniform_even_disc_bounds u (hQ u u.property) hEven
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

end Kneser.HigherMovingSeed

end
