import Kneser.CanonicalHighImaginaryAsymptotics

/-! One inverse on the actual open image of an injective holomorphic map.
All local inverse charts consequently agree; holomorphy and open image are
proved from the genuine nonzero derivative. -/

set_option autoImplicit false
noncomputable section
namespace Kneser.HolomorphicInjectiveInverse

open Filter Set
open scoped Topology

def imageInverse (F : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ F '' U then Classical.choose hz else 0

theorem imageInverse_spec (F : ℂ → ℂ) (U : Set ℂ) (z : ℂ) (hz : z ∈ F '' U) :
    imageInverse F U z ∈ U ∧ F (imageInverse F U z) = z := by
  classical
  simp only [imageInverse, dite_eq_ite, hz, ↓reduceDIte]
  exact Classical.choose_spec hz

theorem imageInverse_left (F : ℂ → ℂ) (U : Set ℂ) (hi : InjOn F U) (z : ℂ) (hz : z ∈ U) :
    imageInverse F U (F z) = z := by
  obtain ⟨hv, he⟩ := imageInverse_spec F U (F z) ⟨z, hz, rfl⟩
  exact hi hv hz he

theorem image_isOpen (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hF : ∀ z ∈ U, AnalyticAt ℂ F z ∧ deriv F z ≠ 0) : IsOpen (F '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨z, hz, rfl⟩
  have hm : F '' U ∈ Filter.map F (𝓝 z) := Filter.image_mem_map (hU.mem_nhds hz)
  rw [(hF z hz).1.hasStrictDerivAt.map_nhds_eq (hF z hz).2] at hm
  exact hm

theorem analyticOnNhd_imageInverse (F : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hi : InjOn F U) (hF : ∀ z ∈ U, AnalyticAt ℂ F z ∧ deriv F z ≠ 0) :
    AnalyticOnNhd ℂ (imageInverse F U) (F '' U) := by
  have hdiff : DifferentiableOn ℂ (imageInverse F U) (F '' U) := by
    rintro _ ⟨z, hz, rfl⟩
    have hn : ∀ᶠ w in 𝓝 z, w ∈ U := hU.mem_nhds hz
    have hleft : ∀ᶠ w in 𝓝 z, imageInverse F U (F w) = w :=
      hn.mono (fun w hw => imageInverse_left F U hi w hw)
    exact ((hF z hz).1.hasStrictDerivAt.to_local_left_inverse (hF z hz).2 hleft).hasDerivAt.differentiableAt.differentiableWithinAt
  exact fun z hz => hdiff.analyticAt ((image_isOpen F U hU hF).mem_nhds hz)

theorem chart_agrees (F : ℂ → ℂ) (U : Set ℂ) (hi : InjOn F U)
    (V : ℂ → ℂ) (W : Set ℂ) (hV : ∀ z ∈ W, V z ∈ U ∧ F (V z) = z) :
    EqOn V (imageInverse F U) W := by
  intro z hz
  obtain ⟨hv, he⟩ := hV z hz
  have hh := imageInverse_left F U hi (V z) hv
  rw [he] at hh
  exact hh.symm

end Kneser.HolomorphicInjectiveInverse
end
