import Kneser.UniformAnalyticParameter
import Kneser.CauchyHeadTaylor

/-!
A compact-uniform expansion survives genuine finite analytic transport.
Common parameter discs, source images and Taylor estimates are all derived.
-/

noncomputable section

namespace Kneser.UniformFiniteCoordinateTransport

open Set Filter Metric
open scoped Topology

theorem uniform_moving_evaluation (A : ℝ → ℂ → ℂ) (D : ℂ → ℂ)
    (W : ℂ × ℂ → ℂ) (S V : Set ℂ) (hS : IsCompact S) (hV : IsOpen V)
    (hW : ∀ u ∈ S, AnalyticAt ℂ W (0, u))
    (hwV : ∀ u ∈ S, W (0, u) ∈ V)
    (hA : ∀ v ∈ V, AnalyticAt ℂ (A 0) v)
    (hD : ∀ v ∈ V, AnalyticAt ℂ D v)
    (hexp : ∀ K : Set ℂ, IsCompact K → K ⊆ V →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ K,
        ‖A s u - A 0 u - (s : ℂ) * D u‖ ≤ C * s ^ (6 / 5 : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ u ∈ S,
      ‖A s (W (s, u)) - A 0 (W (0, u)) -
        (s : ℂ) * (D (W (0, u)) + deriv (fun z : ℂ => A 0 (W (z, u))) 0)‖ ≤
          C * s ^ (6 / 5 : ℝ) := by
  let QA : ℂ × ℂ → ℂ := fun p => A 0 (W p)
  let QD : ℂ × ℂ → ℂ := fun p => D (W p)
  have hQA : ∀ u ∈ S, AnalyticAt ℂ QA (0, u) :=
    fun u hu => (hA _ (hwV u hu)).comp (hW u hu)
  have hQD : ∀ u ∈ S, AnalyticAt ℂ QD (0, u) :=
    fun u hu => (hD _ (hwV u hu)).comp (hW u hu)
  obtain ⟨rA, MA, hrA, hMA, hbA⟩ :=
    UniformAnalyticParameter.exists_compact_disc_bounds QA S hS hQA
  obtain ⟨rD, MD, hrD, hMD, hbD⟩ :=
    UniformAnalyticParameter.exists_compact_disc_bounds QD S hS hQD
  obtain ⟨K, hK, hKV, hwK⟩ :=
    UniformAnalyticParameter.exists_compact_image_neighborhood W S V hS hV hW hwV
  obtain ⟨C₀, hC₀, herror⟩ := hexp K hK hKV
  let CA : ℝ := 2 * MA / rA ^ 2
  let CD : ℝ := 2 * MD / rD ^ 2 + MD / rD
  have hCA : 0 ≤ CA := by dsimp [CA]; positivity
  have hCD : 0 ≤ CD := by dsimp [CD]; positivity
  have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
  have hle : ∀ᶠ s : ℝ in 𝓝[>] 0, s ≤ 1 :=
    ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).mono fun _ h => h.le).filter_mono
      nhdsWithin_le_nhds
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, s < min (rA / 2) (rD / 2) :=
    (eventually_lt_nhds (lt_min (by positivity) (by positivity))).filter_mono nhdsWithin_le_nhds
  refine ⟨C₀ + CA + CD, by positivity, ?_⟩
  filter_upwards [herror, hwK, hpos, hle, hsmall] with s hs hws hsp hs1 hsr
  intro u hu
  have hsA : ‖(s : ℂ)‖ ≤ rA / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
    exact (hsr.trans_le (min_le_left _ _)).le
  have hsD : ‖(s : ℂ)‖ ≤ rD / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp]
    exact (hsr.trans_le (min_le_right _ _)).le
  have hRA := CauchyHeadTaylor.norm_first_remainder_le (fun z => QA (z, u)) rA MA s hrA hMA
    (hbA u hu).1 (fun z hz => (hbA u hu).2 z (sphere_subset_closedBall hz)) hsA
  have hRD := CauchyHeadTaylor.norm_first_remainder_le (fun z => QD (z, u)) rD MD s hrD hMD
    (hbD u hu).1 (fun z hz => (hbD u hu).2 z (sphere_subset_closedBall hz)) hsD
  have hdD := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := (0 : ℂ)) hrD
    (hbD u hu).1 (fun z hz => (hbD u hu).2 z (sphere_subset_closedBall hz))
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp] at hRA hRD
  have hRA' : ‖QA (s, u) - QA (0, u) - (s : ℂ) * deriv (fun z => QA (z, u)) 0‖ ≤
      CA * s ^ 2 := by convert hRA using 1; dsimp [CA]; ring
  have hRD' : ‖QD (s, u) - QD (0, u) - (s : ℂ) * deriv (fun z => QD (z, u)) 0‖ ≤
      (2 * MD / rD ^ 2) * s ^ 2 := by convert hRD using 1; ring
  have hDlinear : ‖QD (s, u) - QD (0, u)‖ ≤ CD * s := by
    have he : QD (s, u) - QD (0, u) =
        (QD (s, u) - QD (0, u) - (s : ℂ) * deriv (fun z => QD (z, u)) 0) +
          (s : ℂ) * deriv (fun z => QD (z, u)) 0 := by ring
    rw [he]
    have ht := norm_add_le
      (QD (s, u) - QD (0, u) - (s : ℂ) * deriv (fun z => QD (z, u)) 0)
      ((s : ℂ) * deriv (fun z => QD (z, u)) 0)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp] at ht
    have hm := mul_le_mul_of_nonneg_left hdD hsp.le
    have hs2 : s ^ 2 ≤ s := by nlinarith
    have hb := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 2 * MD / rD ^ 2)
    calc
      _ ≤ ‖QD (s, u) - QD (0, u) - (s : ℂ) * deriv (fun z => QD (z, u)) 0‖ +
          s * ‖deriv (fun z => QD (z, u)) 0‖ := ht
      _ ≤ (2 * MD / rD ^ 2) * s ^ 2 + s * (MD / rD) := add_le_add hRD' hm
      _ ≤ (2 * MD / rD ^ 2) * s + s * (MD / rD) := add_le_add hb le_rfl
      _ = CD * s := by dsimp [CD]; ring
  have hp : s ^ 2 ≤ s ^ (6 / 5 : ℝ) := by
    simpa [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hsp hs1
      (by norm_num : (6 / 5 : ℝ) ≤ 2)
  have heq : A s (W (s, u)) - A 0 (W (0, u)) -
      (s : ℂ) * (D (W (0, u)) + deriv (fun z => A 0 (W (z, u))) 0) =
      (A s (W (s, u)) - A 0 (W (s, u)) - (s : ℂ) * D (W (s, u))) +
      (QA (s, u) - QA (0, u) - (s : ℂ) * deriv (fun z => QA (z, u)) 0) +
      (s : ℂ) * (QD (s, u) - QD (0, u)) := by dsimp [QA, QD]; ring
  rw [heq]
  have ht := (norm_add_le
    ((A s (W (s, u)) - A 0 (W (s, u)) - (s : ℂ) * D (W (s, u))) +
      (QA (s, u) - QA (0, u) - (s : ℂ) * deriv (fun z => QA (z, u)) 0))
    ((s : ℂ) * (QD (s, u) - QD (0, u)))).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsp] at ht
  have hparam := hs _ (hws u hu)
  have hlin := mul_le_mul_of_nonneg_left hDlinear hsp.le
  have hpa := mul_le_mul_of_nonneg_left hp hCA
  have hpd := mul_le_mul_of_nonneg_left hp hCD
  calc
    _ ≤ ‖A s (W (s, u)) - A 0 (W (s, u)) - (s : ℂ) * D (W (s, u))‖ +
        ‖QA (s, u) - QA (0, u) - (s : ℂ) * deriv (fun z => QA (z, u)) 0‖ +
        s * ‖QD (s, u) - QD (0, u)‖ := ht
    _ ≤ C₀ * s ^ (6 / 5 : ℝ) + CA * s ^ 2 + s * (CD * s) :=
      add_le_add (add_le_add hparam hRA') hlin
    _ = C₀ * s ^ (6 / 5 : ℝ) + CA * s ^ 2 + CD * s ^ 2 := by ring
    _ ≤ C₀ * s ^ (6 / 5 : ℝ) + CA * s ^ (6 / 5 : ℝ) + CD * s ^ (6 / 5 : ℝ) :=
      add_le_add (add_le_add le_rfl hpa) hpd
    _ = _ := by ring

end Kneser.UniformFiniteCoordinateTransport

end
