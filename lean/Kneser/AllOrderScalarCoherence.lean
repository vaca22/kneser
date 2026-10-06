import Kneser.AllOrderScalarAnalytic
import Kneser.UniformAsymptoticTruncation

/-! The finite coefficient lists are coherent across Taylor orders.
Truncation is derived from the true remainder, and uniqueness produces
one coefficient sequence with all finite expansions. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.AllOrderScalarCoherence

open Filter Set
open scoped Topology
open Kneser.AllOrderGateFourier Kneser.AllOrderScalarAnalytic

theorem scalarExpansion_eventually_bounded {f : ℝ → ℂ} {c : ℕ → ℂ} {m : ℕ}
    (hf : ScalarExpansion f c m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ‖f s‖ ≤ B := by
  obtain ⟨C, hC, he⟩ := hf.2
  have ht := (analyticAt_scalarPolynomial c m 0).continuousAt.tendsto.comp tendsto_real_parameter
  have hb : ∀ᶠ s : ℝ in 𝓝[>] 0, ‖scalarPolynomial c m (s : ℂ)‖ ≤ ‖c 0‖ + 1 := by
    have ht' : Tendsto (fun s : ℝ => scalarPolynomial c m (s : ℂ)) (𝓝[>] 0) (𝓝 (c 0)) := by
      convert ht using 1
      · rfl
      · rw [scalarPolynomial_zero]
    exact (ht'.norm.eventually (gt_mem_nhds (by linarith : ‖c 0‖ < ‖c 0‖ + 1))).mono
      fun _ hs => hs.le
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ hs => hs.le).filter_mono
      nhdsWithin_le_nhds
  refine ⟨C + ‖c 0‖ + 1, by positivity, ?_⟩
  filter_upwards [he, hb, hle, self_mem_nhdsWithin] with s hs hbs hs1 hsp
  change 0 < s at hsp
  have hp : s ^ (m + 1) ≤ 1 := pow_le_one₀ hsp.le hs1
  have ht : ‖f s‖ ≤ ‖f s - scalarPolynomial c m (s : ℂ)‖ + ‖scalarPolynomial c m (s : ℂ)‖ := by
    simpa using norm_add_le (f s - scalarPolynomial c m (s : ℂ)) (scalarPolynomial c m (s : ℂ))
  exact ht.trans ((add_le_add (hs.trans (mul_le_mul_of_nonneg_left hp hC)) hbs).trans_eq (by ring))

theorem scalarExpansion_truncate {f : ℝ → ℂ} {c : ℕ → ℂ} {M m : ℕ}
    (hf : ScalarExpansion f c M) (hm : m ≤ M) : ScalarExpansion f c m := by
  obtain ⟨C, hC, he⟩ := hf.2
  obtain ⟨B, _, hb⟩ := scalarExpansion_eventually_bounded hf
  have he' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ (univ : Set Unit),
      ‖f s - Kneser.AsymptoticCoefficientUniqueness.polynomial c M s‖ ≤ C * s ^ ((M : ℝ) + 1) := by
    filter_upwards [he] with s hs _ _
    simpa only [show (M : ℝ) + 1 = ((M + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, Kneser.AsymptoticCoefficientUniqueness.polynomial,
      scalarPolynomial] using hs
  have hb' : ∀ᶠ s : ℝ in 𝓝[>] 0, ∃ B : ℝ, ∀ u ∈ (univ : Set Unit), ‖f s‖ ≤ B := by
    filter_upwards [hb] with s hs
    exact ⟨B, fun _ _ => hs⟩
  obtain ⟨D, hD, hd⟩ := Kneser.AsymptoticCoefficientUniqueness.truncate_uniform_integer
    (fun s (_ : Unit) => f s) (fun j (_ : Unit) => c j) M m hm univ C hC he' hb'
  refine ⟨hf.1, D, hD, ?_⟩
  filter_upwards [hd] with s hs
  have h := hs () (mem_univ ())
  simpa only [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, Kneser.AsymptoticCoefficientUniqueness.polynomial,
    scalarPolynomial] using h

theorem scalarExpansion_unique {f : ℝ → ℂ} {c d : ℕ → ℂ} {m : ℕ}
    (hc : ScalarExpansion f c m) (hd : ScalarExpansion f d m) :
    ∀ j ≤ m, c j = d j := by
  obtain ⟨C, hC, hec⟩ := hc.2
  obtain ⟨D, hD, hed⟩ := hd.2
  exact Kneser.FiniteLocalExpansionGluing.coefficients_unique_integer f c d m C D hC hD hec hed

theorem exists_coherent_coefficients (f : ℝ → ℂ)
    (h : ∀ m : ℕ, ∃ c : ℕ → ℂ, ScalarExpansion f c m) :
    ∃ c : ℕ → ℂ, ∀ m : ℕ, ScalarExpansion f c m := by
  choose a ha using h
  let c : ℕ → ℂ := fun j => a j j
  have hc (m j : ℕ) (hj : j ≤ m) : c j = a m j :=
    scalarExpansion_unique (ha j) (scalarExpansion_truncate (ha m) hj) j le_rfl
  refine ⟨c, ?_⟩
  intro m
  have hpoly (s : ℂ) : scalarPolynomial c m s = scalarPolynomial (a m) m s := by
    unfold scalarPolynomial
    apply Finset.sum_congr rfl
    intro j hj
    rw [hc m j (by simpa using Finset.mem_range.mp hj)]
  obtain ⟨C, hC, he⟩ := (ha m).2
  refine ⟨(hc m 0 (Nat.zero_le m)).trans (ha m).1, C, hC, ?_⟩
  simpa only [hpoly] using he

theorem exists_coherent_positive_orders (f : ℝ → ℂ)
    (h : ∀ m : ℕ, 1 ≤ m → ∃ c : ℕ → ℂ, ScalarExpansion f c m) :
    ∃ c : ℕ → ℂ, ∀ m : ℕ, ScalarExpansion f c m := by
  apply exists_coherent_coefficients f
  intro m
  by_cases hm : 1 ≤ m
  · exact h m hm
  · obtain ⟨c, hc⟩ := h 1 le_rfl
    exact ⟨c, scalarExpansion_truncate hc (by omega)⟩

end Kneser.AllOrderScalarCoherence

end
