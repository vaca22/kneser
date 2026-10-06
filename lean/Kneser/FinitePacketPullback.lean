import Kneser.ActualHigherFinitePacket

/-! Genuine spatial changes of chart preserve the finite coordinate data;
compact sets and their parameter neighborhoods are transported in the proof. -/

noncomputable section
namespace Kneser.FinitePacketPullback

open Filter Set Kneser.ActualHigherFinitePacket
open Kneser.FiniteExpansionHolomorphy
open scoped Topology

theorem normalizedFiniteData_pullback (f : ℝ → ℂ → ℂ) (c : ℕ → ℂ → ℂ)
    (d q : ℂ → ℂ) (m : ℕ) (U V : Set ℂ)
    (h : NormalizedFiniteData f c d m U)
    (hq : AnalyticOnNhd ℂ q V) (hm : MapsTo q V U) :
    NormalizedFiniteData (fun s z => f s (q z)) (fun j z => c j (q z))
      (fun z => d (q z)) m V := by
  refine ⟨?_, ?_, ?_⟩
  · intro j hj z hz
    exact (h.1 j hj _ (hm hz)).comp_of_eq (hq z hz) rfl
  · intro z hz
    exact h.2.1 _ (hm hz)
  · intro j hj K hK hKV
    have hKi : IsCompact (q '' K) := hK.image_of_continuousOn (hq.continuousOn.mono hKV)
    have hKsub : q '' K ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      exact hm (hKV hz)
    obtain ⟨C, hC, hb⟩ := h.2.2 j hj _ hKi hKsub
    exact ⟨C, hC, hb.mono fun s hs z hz => hs _ (mem_image_of_mem _ hz)⟩

end Kneser.FinitePacketPullback
