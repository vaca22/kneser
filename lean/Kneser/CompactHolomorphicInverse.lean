import Kneser.StableHolomorphicInverse
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Common moving inverse neighborhoods of compact image sets

The base inverse is proved holomorphic by the actual inverse-function theorem.
After transport to base image coordinates, the moving maps converge uniformly
to the identity. Local Banach inverses agree on overlaps because both are
uniformly close to the same image point. This constructs the common inverse,
without assuming a moving inverse or its continuity.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.CompactHolomorphicInverse

open Filter Set Metric
open scoped Topology

/-- An injective holomorphic map with nonzero derivative has a genuine
holomorphic inverse on its open image. -/
theorem exists_base_inverse (S : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hS : AnalyticOnNhd ℂ S U) (hd : ∀ u ∈ U, deriv S u ≠ 0) (hinj : InjOn S U) :
    IsOpen (S '' U) ∧ ∃ V : ℂ → ℂ,
      (∀ z ∈ S '' U, V z ∈ U ∧ S (V z) = z) ∧
      (∀ u ∈ U, V (S u) = u) ∧ AnalyticOnNhd ℂ V (S '' U) := by
  have hΩ : IsOpen (S '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro _ ⟨u, hu, rfl⟩
    rw [← (hS u hu).hasStrictDerivAt.map_nhds_eq (hd u hu)]
    exact Filter.image_mem_map (hU.mem_nhds hu)
  let V := Function.invFunOn S U
  have hV : ∀ z ∈ S '' U, V z ∈ U ∧ S (V z) = z := by
    rintro z ⟨u, hu, heq⟩
    exact Function.invFunOn_pos ⟨u, hu, heq⟩
  have hleft : ∀ u ∈ U, V (S u) = u := hinj.leftInvOn_invFunOn
  refine ⟨hΩ, V, hV, hleft, ?_⟩
  intro z hz
  have hv := hV z hz
  have hlocal : ∀ᶠ u in 𝓝 (V z), V (S u) = u :=
    (show ∀ᶠ u in 𝓝 (V z), u ∈ U from hU.mem_nhds hv.1).mono fun u hu => hleft u hu
  have hder := (hS (V z) hv.1).hasStrictDerivAt.to_local_left_inverse (hd _ hv.1) hlocal
  rw [hv.2] at hder
  have hdiff : DifferentiableOn ℂ V (S '' U) := by
    intro w hw
    have hvw := hV w hw
    have hlocalw : ∀ᶠ u in 𝓝 (V w), V (S u) = u :=
      (show ∀ᶠ u in 𝓝 (V w), u ∈ U from hU.mem_nhds hvw.1).mono fun u hu => hleft u hu
    have hdw := (hS (V w) hvw.1).hasStrictDerivAt.to_local_left_inverse (hd _ hvw.1) hlocalw
    rw [hvw.2] at hdw
    exact hdw.hasDerivAt.differentiableAt.differentiableWithinAt
  exact hdiff.analyticAt (hΩ.mem_nhds hz)

/-- Uniform convergence on compact subsets, stated with a direct norm bound. -/
def CompactUniformConvergence (F : ℝ → ℂ → ℂ) (G : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ P : Set ℂ, IsCompact P → P ⊆ U → ∀ ε > 0,
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ x ∈ P, ‖F s x - G x‖ ≤ ε

/-- The geometric compact tube used to glue all local charts has one common
positive radius; no finite-chart coverage assumption is needed. -/
theorem exists_compact_image_tube (Ω K : Set ℂ) (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ r > 0, ∃ P : Set ℂ, IsCompact P ∧ P ⊆ Ω ∧
      (∀ b ∈ K, closedBall b (4 * r) ⊆ P) := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  refine ⟨δ / 4, by positivity, cthickening δ K, hK.cthickening, hsub, ?_⟩
  intro b hb
  have heq : 4 * (δ / 4) = δ := by ring
  rw [heq]
  exact closedBall_subset_cthickening hb δ

/-- Construction and overlap compatibility of moving inverses for maps
converging to the identity. A common open neighborhood of the full compact
set is constructed; the output converges uniformly on that neighborhood. -/
theorem exists_compact_identity_inverse (F : ℝ → ℂ → ℂ) (Ω K : Set ℂ)
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (h0 : ∀ z ∈ Ω, F 0 z = z)
    (ha : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (F s) Ω)
    (hconv : CompactUniformConvergence F id Ω) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ W ⊆ Ω ∧
    ∃ P : Set ℂ, IsCompact P ∧ P ⊆ Ω ∧ W ⊆ P ∧
    ∃ V : ℝ → ℂ → ℂ,
      (∀ z ∈ W, V 0 z = z) ∧ AnalyticOnNhd ℂ (V 0) W ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ z ∈ W, V s z ∈ P ∧ F s (V s z) = z) ∧ AnalyticOnNhd ℂ (V s) W) ∧
      (∀ ε > 0, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ W, ‖V s z - z‖ ≤ ε) := by
  obtain ⟨r, hr, P, hPc, hPΩ, hballs⟩ := exists_compact_image_tube Ω K hΩ hK hKΩ
  let W : Set ℂ := ⋃ b ∈ K, ball b (r / 4)
  have hWo : IsOpen W := isOpen_biUnion fun b hb => isOpen_ball
  have hKW : K ⊆ W := by
    intro b hb
    exact mem_iUnion₂.mpr ⟨b, hb, mem_ball_self (by positivity)⟩
  have hWP : W ⊆ P := by
    intro z hz
    obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.mp hz
    apply hballs b hb
    have hn : dist z b < r / 4 := hzb
    change dist z b ≤ 4 * r
    linarith
  let Good : ℝ → Prop := fun s =>
    AnalyticOnNhd ℂ (F s) Ω ∧ ∀ x ∈ P, ‖F s x - x‖ ≤ r / 16
  have hg0 : Good 0 := by
    refine ⟨?_, fun x hx => by rw [h0 _ (hPΩ hx), sub_self, norm_zero]; positivity⟩
    intro x hx
    apply (analyticAt_id (𝕜 := ℂ) (z := x)).congr
    exact (show ∀ᶠ w in 𝓝 x, w ∈ Ω from hΩ.mem_nhds hx).mono fun w hw => (h0 w hw).symm
  have hg : ∀ᶠ s : ℝ in 𝓝[>] 0, Good s := by
    filter_upwards [ha, hconv P hPc hPΩ (r / 16) (by positivity)] with s hs hc
    exact ⟨hs, hc⟩
  let G : ℝ → ℂ → ℂ → ℂ := fun s b w => F s (b + w) - b
  have hlocal (s : ℝ) (hs : Good s) (b : ℂ) (hb : b ∈ K) :
      ∃ v : ℂ → ℂ,
        (∀ z ∈ ball b (r / 4), v z ∈ closedBall b r ∧ F s (v z) = z ∧ ‖v z - z‖ ≤ r / 16) ∧
        AnalyticOnNhd ℂ v (ball b (r / 4)) ∧
        ApproximatesLinearOn (G s b) (ContinuousLinearMap.id ℂ ℂ) (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    have hGa : AnalyticOnNhd ℂ (G s b) (closedBall (0 : ℂ) (4 * r)) := by
      intro w hw
      have hbw : b + w ∈ P := hballs b hb (by simpa [mem_closedBall, dist_eq_norm] using hw)
      have haff : AnalyticAt ℂ (fun v : ℂ => b + v) w := analyticAt_const.add analyticAt_id
      have h : AnalyticAt ℂ (fun v : ℂ => F s (b + v)) w :=
        (hs.1 _ (hPΩ hbw)).comp_of_eq haff rfl
      exact h.sub analyticAt_const
    have hGdiff : DiffContOnCl ℂ (G s b) (ball (0 : ℂ) (4 * r)) := by
      apply DifferentiableOn.diffContOnCl
      exact hGa.differentiableOn.mono closure_ball_subset_closedBall
    have hGb : ∀ w ∈ closedBall (0 : ℂ) (4 * r), ‖G s b w - w‖ ≤ r / 16 := by
      intro w hw
      have hbw : b + w ∈ P := hballs b hb (by simpa [mem_closedBall, dist_eq_norm] using hw)
      convert hs.2 _ hbw using 1
      congr 1
      dsimp [G]
      ring
    have hid : ApproximatesLinearOn (id : ℂ → ℂ) (ContinuousLinearMap.id ℂ ℂ)
        (ball (0 : ℂ) (2 * r)) (1 / 4) := by intro x hx y hy; simp
    have happ := Kneser.StableHolomorphicInverse.approximates_identity_of_disc_error
      id (G s b) r (r / 16) hr hid (by
        convert hGdiff.sub differentiable_id.diffContOnCl using 1
        funext w
        rfl) hGb (by linarith)
    have hcenter : ‖G s b 0‖ ≤ r / 4 := by
      have h := hGb 0 (by simp; positivity)
      simp only [sub_zero] at h
      linarith
    have hGa' : AnalyticOnNhd ℂ (G s b) (ball (0 : ℂ) (2 * r)) := by
      intro w hw
      apply hGa w
      have hn : ‖w‖ < 2 * r := by simpa [mem_ball, dist_zero_right] using hw
      simp only [mem_closedBall, dist_zero_right]; linarith
    obtain ⟨v, hv, hav, _⟩ := Kneser.StableHolomorphicInverse.exists_holomorphic_inverse_on_disc
      (G s b) r hr happ hGa' hcenter
    let v' : ℂ → ℂ := fun z => b + v (z - b)
    refine ⟨v', ?_, ?_, happ⟩
    · intro z hz
      have hz' : z - b ∈ ball (0 : ℂ) (r / 4) := by simpa [mem_ball, dist_eq_norm] using hz
      have hvz := hv _ hz'
      have hpre : v' z ∈ closedBall b r := by simpa [v', mem_closedBall, dist_eq_norm] using hvz.1
      have heq : F s (v' z) = z := by
        have h := hvz.2
        change F s (v' z) - b = z - b at h
        linear_combination h
      refine ⟨hpre, heq, ?_⟩
      calc
        ‖v' z - z‖ = ‖F s (v' z) - v' z‖ := by rw [heq, norm_sub_rev]
        _ ≤ r / 16 := hs.2 _ (hballs b hb (by
          have hn : dist (v' z) b ≤ r := hpre
          change dist (v' z) b ≤ 4 * r; linarith))
    · intro z hz
      have hz' : z - b ∈ ball (0 : ℂ) (r / 4) := by simpa [mem_ball, dist_eq_norm] using hz
      exact analyticAt_const.add ((hav _ hz').comp_of_eq
        (analyticAt_id.sub analyticAt_const) rfl)
  have hex : ∀ s : ℝ × ℂ, ∃ v : ℂ → ℂ,
      Good s.1 → s.2 ∈ K →
        (∀ z ∈ ball s.2 (r / 4), v z ∈ closedBall s.2 r ∧ F s.1 (v z) = z ∧ ‖v z - z‖ ≤ r / 16) ∧
        AnalyticOnNhd ℂ v (ball s.2 (r / 4)) ∧
        ApproximatesLinearOn (G s.1 s.2) (ContinuousLinearMap.id ℂ ℂ)
          (ball (0 : ℂ) (2 * r)) (1 / 2) := by
    intro p
    by_cases hs : Good p.1 ∧ p.2 ∈ K
    · obtain ⟨v, hv, hav, happ⟩ := hlocal p.1 hs.1 p.2 hs.2
      exact ⟨v, fun _ _ => ⟨hv, hav, happ⟩⟩
    · exact ⟨id, fun hgood hmem => False.elim (hs ⟨hgood, hmem⟩)⟩
  let L : ℝ → ℂ → ℂ → ℂ := fun s b => Classical.choose (hex (s,b))
  have hL (s : ℝ) (hs : Good s) (b : ℂ) (hb : b ∈ K) := Classical.choose_spec (hex (s,b)) hs hb
  have hcompat (s : ℝ) (hs : Good s) (b c z : ℂ) (hb : b ∈ K) (hc : c ∈ K)
      (hzb : z ∈ ball b (r / 4)) (hzc : z ∈ ball c (r / 4)) : L s b z = L s c z := by
    have hbv := (hL s hs b hb).1 z hzb
    have hcv := (hL s hs c hc).1 z hzc
    have hdist : dist (L s c z) b < 2 * r := by
      have hn := dist_triangle (L s c z) z b
      have hcz : dist (L s c z) z ≤ r / 16 := by simpa [dist_eq_norm] using hcv.2.2
      have hzb' : dist z b < r / 4 := hzb
      linarith
    have hdistb : dist (L s b z) b < 2 * r := by have hn : dist (L s b z) b ≤ r := hbv.1; linarith
    have h := Kneser.StableHolomorphicInverse.norm_sub_le_two_mul_norm_image_sub
      (G s b) r (hL s hs b hb).2.2 (L s b z - b) (L s c z - b)
      (by simpa [mem_ball, dist_eq_norm] using hdistb)
      (by simpa [mem_ball, dist_eq_norm] using hdist)
    have hbeq : F s (L s b z) = z := hbv.2.1
    have hceq : F s (L s c z) = z := hcv.2.1
    have heqb : G s b (L s b z - b) = z - b := by simp [G, hbeq]
    have heqc : G s b (L s c z - b) = z - b := by simp [G, hceq]
    rw [heqb, heqc, sub_self, norm_zero, mul_zero] at h
    have he := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
    linear_combination he
  have hcenter : ∀ z : ℂ, ∃ b : ℂ, z ∈ W → b ∈ K ∧ z ∈ ball b (r / 4) := by
    intro z
    by_cases hz : z ∈ W
    · obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.mp hz
      exact ⟨b, fun _ => ⟨hb, hzb⟩⟩
    · exact ⟨0, fun h => False.elim (hz h)⟩
  let center : ℂ → ℂ := fun z => Classical.choose (hcenter z)
  have hc (z : ℂ) (hz : z ∈ W) : center z ∈ K ∧ z ∈ ball (center z) (r / 4) :=
    Classical.choose_spec (hcenter z) hz
  let V : ℝ → ℂ → ℂ := fun s z => L s (center z) z
  have hglobal (s : ℝ) (hs : Good s) :
      (∀ z ∈ W, V s z ∈ P ∧ F s (V s z) = z) ∧ AnalyticOnNhd ℂ (V s) W := by
    refine ⟨?_, ?_⟩
    · intro z hz
      have h := (hL s hs (center z) (hc z hz).1).1 z (hc z hz).2
      refine ⟨hballs _ (hc z hz).1 ?_, h.2.1⟩
      have hn : dist (V s z) (center z) ≤ r := h.1
      change dist (V s z) (center z) ≤ 4 * r; linarith
    · intro z hz
      let b := center z
      have hb := (hc z hz).1
      have hzb := (hc z hz).2
      apply ((hL s hs b hb).2.1 z hzb).congr
      have hnh : ∀ᶠ w in 𝓝 z, w ∈ ball b (r / 4) := isOpen_ball.mem_nhds hzb
      filter_upwards [hnh] with w hw
      have hwW : w ∈ W := mem_iUnion₂.mpr ⟨b, hb, hw⟩
      exact hcompat s hs b (center w) w hb (hc w hwW).1 hw (hc w hwW).2
  have hV0 : ∀ z ∈ W, V 0 z = z := by
    intro z hz
    have hv := (hglobal 0 hg0).1 z hz
    rw [h0 _ (hPΩ hv.1)] at hv
    exact hv.2
  refine ⟨W, hWo, hKW, hWP.trans hPΩ, P, hPc, hPΩ, hWP, V, hV0, (hglobal 0 hg0).2,
    hg.mono (fun s hs => hglobal s hs), ?_⟩
  intro ε hε
  filter_upwards [hg, hconv P hPc hPΩ ε hε] with s hs he
  intro z hz
  have hv := (hglobal s hs).1 z hz
  calc
    ‖V s z - z‖ = ‖F s (V s z) - V s z‖ := by rw [hv.2, norm_sub_rev]
    _ ≤ ε := he _ hv.1

/-- A common inverse neighborhood of any compact subset of the true base
image. Branch existence, compatibility, spatial holomorphy, and uniform
parameter convergence are conclusions, not hypotheses. -/
theorem exists_compact_holomorphic_inverse (S : ℝ → ℂ → ℂ) (U K : Set ℂ)
    (hU : IsOpen U) (hK : IsCompact K) (hKimage : K ⊆ (S 0) '' U)
    (hS0 : AnalyticOnNhd ℂ (S 0) U) (hd : ∀ u ∈ U, deriv (S 0) u ≠ 0)
    (hinj : InjOn (S 0) U)
    (ha : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (S s) U)
    (hconv : CompactUniformConvergence S (S 0) U) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ W ⊆ (S 0) '' U ∧
    ∃ V : ℝ → ℂ → ℂ,
      (∀ z ∈ W, V 0 z ∈ U ∧ S 0 (V 0 z) = z) ∧ AnalyticOnNhd ℂ (V 0) W ∧
      (∀ᶠ s : ℝ in 𝓝[>] 0,
        (∀ z ∈ W, V s z ∈ U ∧ S s (V s z) = z) ∧ AnalyticOnNhd ℂ (V s) W) ∧
      (∀ ε > 0, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ z ∈ K, ‖V s z - V 0 z‖ ≤ ε) := by
  obtain ⟨hΩ, B, hB, hBleft, hBa⟩ := exists_base_inverse (S 0) U hU hS0 hd hinj
  let Ω := (S 0) '' U
  let F : ℝ → ℂ → ℂ := fun s z => S s (B z)
  have hF0 : ∀ z ∈ Ω, F 0 z = z := fun z hz => (hB z hz).2
  have hFa : ∀ᶠ s : ℝ in 𝓝[>] 0, AnalyticOnNhd ℂ (F s) Ω := by
    filter_upwards [ha] with s hs
    intro z hz
    exact (hs _ (hB z hz).1).comp_of_eq (hBa z hz) rfl
  have hFc : CompactUniformConvergence F id Ω := by
    intro P hPc hP ε hε
    have hBc : IsCompact (B '' P) := hPc.image_of_continuousOn (hBa.continuousOn.mono hP)
    have hBU : B '' P ⊆ U := by rintro _ ⟨z, hz, rfl⟩; exact (hB z (hP hz)).1
    filter_upwards [hconv (B '' P) hBc hBU ε hε] with s hs
    intro z hz
    have h := hs (B z) (mem_image_of_mem B hz)
    simpa [F, (hB z (hP hz)).2] using h
  obtain ⟨W, hWo, hKW, hWΩ, P, hPc, hPΩ, hWP, T, hT0, hTa0, hT, hTc⟩ :=
    exists_compact_identity_inverse F Ω K hΩ hK hKimage hF0 hFa hFc
  let V : ℝ → ℂ → ℂ := fun s z => B (T s z)
  have hV0eq : ∀ z ∈ W, V 0 z = B z := fun z hz => congrArg B (hT0 z hz)
  have hV0 : ∀ z ∈ W, V 0 z ∈ U ∧ S 0 (V 0 z) = z := by
    intro z hz
    rw [hV0eq z hz]
    exact hB z (hWΩ hz)
  have hVa0 : AnalyticOnNhd ℂ (V 0) W := by
    intro z hz
    exact (hBa z (hWΩ hz)).comp_of_eq (hTa0 z hz) (hT0 z hz)
  have hV : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (∀ z ∈ W, V s z ∈ U ∧ S s (V s z) = z) ∧ AnalyticOnNhd ℂ (V s) W := by
    filter_upwards [hT] with s hs
    refine ⟨?_, ?_⟩
    · intro z hz
      have ht := hs.1 z hz
      exact ⟨(hB _ (hPΩ ht.1)).1, ht.2⟩
    · intro z hz
      exact (hBa _ (hPΩ (hs.1 z hz).1)).comp_of_eq (hs.2 z hz) rfl
  refine ⟨W, hWo, hKW, hWΩ, V, hV0, hVa0, hV, ?_⟩
  intro ε hε
  have hUC := hPc.uniformContinuousOn_of_continuous (hBa.continuousOn.mono hPΩ)
  obtain ⟨δ, hδ, hδB⟩ := Metric.uniformContinuousOn_iff.mp hUC ε hε
  filter_upwards [hT, hTc (δ / 2) (by positivity)] with s hs ht
  intro z hz
  have htz := hs.1 z (hKW hz)
  have hnear : dist (T s z) z < δ := by
    have h := ht z (hKW hz)
    rw [dist_eq_norm]
    linarith
  have h := hδB (T s z) htz.1 z (hWP (hKW hz)) hnear
  rw [dist_eq_norm] at h
  simpa [V, hT0 z (hKW hz)] using h.le

end Kneser.CompactHolomorphicInverse

end
