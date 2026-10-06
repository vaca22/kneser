import Kneser.GateInverseDerivative
import Kneser.HeadTail
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

/-!
Finite analytic transport of a compact-uniform coordinate expansion.
The expansion at moving spatial points is derived from the compact theorem;
neither a moving-point remainder nor its derivative is an input.
-/

noncomputable section

namespace Kneser.FiniteCoordinateTransport

open Set Filter Metric
open scoped Topology

theorem hasDerivWithinAt_moving_composition_of_compact_expansion
    (A : ℝ → ℂ → ℂ) (D : ℂ → ℂ) (V : Set ℂ)
    (hV : IsOpen V)
    (hexpansion : ∀ K : Set ℂ, IsCompact K → K ⊆ V →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
        ‖A s u - A 0 u - s • D u‖ ≤ C * s ^ (6 / 5 : ℝ))
    (w : ℝ → ℂ) (dw A' : ℂ)
    (hw : HasDerivWithinAt w dw (Ici 0) 0) (hwV : w 0 ∈ V)
    (hD : ContinuousAt D (w 0)) (hA : HasDerivAt (A 0) A' (w 0)) :
    HasDerivWithinAt (fun s => A s (w s)) (D (w 0) + A' * dw) (Ici 0) 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hwV)
  let K : Set ℂ := closedBall (w 0) (r / 2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKV : K ⊆ V := (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
  obtain ⟨C, hC, herror⟩ := hexpansion K hK hKV
  have ht : Tendsto w (𝓝[>] 0) (𝓝 (w 0)) := hw.Ioi_of_Ici.continuousWithinAt
  have hwK : ∀ᶠ s : ℝ in 𝓝[>] 0, w s ∈ K :=
    ht.eventually (closedBall_mem_nhds _ (by positivity : 0 < r / 2))
  let ε : ℝ → ℝ := fun s => C * s ^ (1 / 5 : ℝ)
  have hε : Tendsto ε (𝓝[>] 0) (𝓝 0) := by
    have hp := (Real.continuousAt_rpow_const (0 : ℝ) (1 / 5) (Or.inr (by norm_num))).tendsto
    simpa [ε, Real.zero_rpow (by norm_num : (1 / 5 : ℝ) ≠ 0)] using
      (tendsto_const_nhds.mul (hp.mono_left nhdsWithin_le_nhds))
  have hrem : ∀ᶠ s : ℝ in 𝓝[>] 0,
      ‖A s (w s) - A 0 (w s) - (s : ℂ) * D (w s)‖ ≤ |s| * ε s := by
    filter_upwards [herror, hwK, self_mem_nhdsWithin] with s hs hws hpos
    have hpos' : 0 < s := hpos
    have hpow : s ^ (6 / 5 : ℝ) = s * s ^ (1 / 5 : ℝ) := by
      rw [show (6 / 5 : ℝ) = 1 + 1 / 5 by norm_num, Real.rpow_add hpos',
        Real.rpow_one]
    simpa only [Complex.real_smul, hpow, abs_of_pos hpos', ε, mul_assoc,
      mul_comm, mul_left_comm] using hs (w s) hws
  exact GateInverseDerivative.hasDerivWithinAt_moving_composition A w D ε A' dw
    hA hw (hD.tendsto.comp ht) hε hrem

end Kneser.FiniteCoordinateTransport

end
