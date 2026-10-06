import Kneser.ParabolicCoordinateJacobian
import Kneser.ActualBilateralGate

/-!
Canonical Fatou coordinates extend by actual finite orbit entry. The
regular entry domain is open, entry times give identical values, and the
extended coordinate is holomorphic with nonzero derivative. Regularity
of the actual gate iterates is already proved by the true dynamics.
-/

set_option autoImplicit false
noncomputable section
namespace Kneser.FatouBasinExtension

open Filter Set Metric
open Kneser.ParabolicExponentialOrbit Kneser.ParabolicFatouHolomorphic
open Kneser.ParabolicCoordinateJacobian
open scoped Topology

def Entry (f : ℂ → ℂ) (U : Set ℂ) (z : ℂ) (n : ℕ) : Prop :=
  (f^[n]) z ∈ U ∧ AnalyticAt ℂ (f^[n]) z ∧ deriv (f^[n]) z ≠ 0

def basin (f : ℂ → ℂ) (U : Set ℂ) : Set ℂ := {z | ∃ n, Entry f U z n}

def transport (f φ : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ := φ ((f^[n]) z) - (n : ℂ)

def extend (f φ : ℂ → ℂ) (U : Set ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ basin f U then transport f φ (Classical.choose hz) z else 0

theorem iterate_mem (f : ℂ → ℂ) (U : Set ℂ) (hmap : MapsTo f U U)
    (z : ℂ) (hz : z ∈ U) (n : ℕ) : (f^[n]) z ∈ U := by
  induction n with
  | zero => simpa using hz
  | succ n ih => simpa only [Function.iterate_succ_apply'] using hmap ih

theorem coordinate_iterate (f φ : ℂ → ℂ) (U : Set ℂ)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (z : ℂ) (hz : z ∈ U) (n : ℕ) : φ ((f^[n]) z) = φ z + (n : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', habel _ (iterate_mem f U hmap z hz n), ih]
    push_cast
    ring

theorem transport_of_entry_le (f φ : ℂ → ℂ) (U : Set ℂ)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (z : ℂ) (n m : ℕ) (hn : (f^[n]) z ∈ U) (hnm : n ≤ m) :
    transport f φ m z = transport f φ n z := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  dsimp only [transport]
  rw [Nat.add_comm n k, Function.iterate_add_apply,
    coordinate_iterate f φ U hmap habel _ hn k]
  push_cast
  ring

theorem transport_independent (f φ : ℂ → ℂ) (U : Set ℂ)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (z : ℂ) (n m : ℕ) (hn : (f^[n]) z ∈ U) (hm : (f^[m]) z ∈ U) :
    transport f φ n z = transport f φ m z := by
  obtain hnm | hmn := le_total n m
  · exact (transport_of_entry_le f φ U hmap habel z n m hn hnm).symm
  · exact transport_of_entry_le f φ U hmap habel z m n hm hmn

theorem extend_eq_transport (f φ : ℂ → ℂ) (U : Set ℂ)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (z : ℂ) (n : ℕ) (hn : Entry f U z n) :
    extend f φ U z = transport f φ n z := by
  have hz : z ∈ basin f U := ⟨n, hn⟩
  rw [extend, dif_pos hz]
  exact transport_independent f φ U hmap habel z _ n (Classical.choose_spec hz).1 hn.1

theorem entry_eventually (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (z : ℂ) (n : ℕ) (hn : Entry f U z n) :
    ∀ᶠ w in 𝓝 z, Entry f U w n := by
  have hm := hn.2.1.continuousAt.eventually (hU.mem_nhds hn.1)
  have ha := hn.2.1.eventually_analyticAt
  have hd := hn.2.1.deriv.continuousAt.eventually (eventually_ne_nhds hn.2.2)
  filter_upwards [hm, ha, hd] with w hwm hwa hwd
  exact ⟨hwm, hwa, hwd⟩

theorem basin_isOpen (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) : IsOpen (basin f U) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨n, hn⟩ := hz
  exact (entry_eventually f U hU z n hn).mono fun w hw => ⟨n, hw⟩

theorem extend_germ (f φ : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (z : ℂ) (n : ℕ) (hn : Entry f U z n) :
    extend f φ U =ᶠ[𝓝 z] transport f φ n :=
  (entry_eventually f U hU z n hn).mono fun w hw =>
    extend_eq_transport f φ U hmap habel w n hw

theorem extend_analytic_jacobian (f φ : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (hφ : ∀ z ∈ U, AnalyticAt ℂ φ z ∧ deriv φ z ≠ 0)
    (z : ℂ) (hz : z ∈ basin f U) :
    AnalyticAt ℂ (extend f φ U) z ∧ deriv (extend f φ U) z ≠ 0 := by
  obtain ⟨n, hn⟩ := hz
  have hg := extend_germ f φ U hU hmap habel z n hn
  have hc := hφ _ hn.1
  have ha : AnalyticAt ℂ (transport f φ n) z :=
    (hc.1.comp hn.2.1).sub analyticAt_const
  have hd := ((hc.1.hasStrictDerivAt.hasDerivAt.comp z hn.2.1.hasStrictDerivAt.hasDerivAt).sub_const
    (n : ℂ)).deriv
  change deriv (transport f φ n) z = deriv φ ((f^[n]) z) * deriv (f^[n]) z at hd
  refine ⟨ha.congr hg.symm, ?_⟩
  rw [hg.deriv_eq, hd]
  exact mul_ne_zero hc.2 hn.2.2

theorem extend_eq_local (f φ : ℂ → ℂ) (U : Set ℂ)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (z : ℂ) (hz : z ∈ U) : extend f φ U z = φ z := by
  have he : Entry f U z 0 := by
    simp only [Entry, Function.iterate_zero, id_eq]
    exact ⟨hz, analyticAt_id, by simp⟩
  simpa [transport] using extend_eq_transport f φ U hmap habel z 0 he

theorem extend_seed_agree (f φ : ℂ → ℂ) (U V : Set ℂ)
    (hU : MapsTo f U U) (hV : MapsTo f V V)
    (hφU : ∀ z ∈ U, φ (f z) = φ z + 1)
    (hφV : ∀ z ∈ V, φ (f z) = φ z + 1)
    (z : ℂ) (hzU : z ∈ basin f U) (hzV : z ∈ basin f V) :
    extend f φ U z = extend f φ V z := by
  obtain ⟨n, hn⟩ := hzU
  obtain ⟨m, hm⟩ := hzV
  rw [extend_eq_transport f φ U hU hφU z n hn,
    extend_eq_transport f φ V hV hφV z m hm]
  exact (transport_of_entry_le f φ U hU hφU z n (n + m) hn.1
    (Nat.le_add_right n m)).symm.trans
      (transport_of_entry_le f φ V hV hφV z m (n + m) hm.1
        (Nat.le_add_left m n))

theorem iterate_analytic_jacobian (f : ℂ → ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z ∧ deriv f z ≠ 0) (z : ℂ) (n : ℕ) :
    AnalyticAt ℂ (f^[n]) z ∧ deriv (f^[n]) z ≠ 0 := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact ⟨analyticAt_id, by simp⟩
  | succ n ih =>
    have hc := hf ((f^[n]) z)
    have hd := (hc.1.hasStrictDerivAt.hasDerivAt.comp z ih.1.hasStrictDerivAt.hasDerivAt).deriv
    rw [Function.iterate_succ']
    exact ⟨hc.1.comp ih.1, by rw [hd]; exact mul_ne_zero hc.2 ih.2⟩

theorem iterate_analytic_jacobian_on (f : ℂ → ℂ) (U : Set ℂ)
    (hmap : MapsTo f U U)
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z ∧ deriv f z ≠ 0)
    (z : ℂ) (hz : z ∈ U) (n : ℕ) :
    AnalyticAt ℂ (f^[n]) z ∧ deriv (f^[n]) z ≠ 0 := by
  induction n with
  | zero => simp only [Function.iterate_zero]; exact ⟨analyticAt_id, by simp⟩
  | succ n ih =>
    have hc := hf _ (iterate_mem f U hmap z hz n)
    have hd := (hc.1.hasStrictDerivAt.hasDerivAt.comp z ih.1.hasStrictDerivAt.hasDerivAt).deriv
    rw [Function.iterate_succ']
    exact ⟨hc.1.comp ih.1, by rw [hd]; exact mul_ne_zero hc.2 ih.2⟩

theorem basin_mono (f : ℂ → ℂ) (U V : Set ℂ) (hUV : U ⊆ V) :
    basin f U ⊆ basin f V := by
  rintro z ⟨n, hn⟩
  exact ⟨n, hUV hn.1, hn.2⟩

theorem basin_subset_of_eventual_entry (f : ℂ → ℂ) (U V : Set ℂ)
    (hmap : MapsTo f U U)
    (hf : ∀ z ∈ U, AnalyticAt ℂ f z ∧ deriv f z ≠ 0)
    (he : ∀ z ∈ U, ∃ k : ℕ, (f^[k]) z ∈ V) :
    basin f U ⊆ basin f V := by
  rintro z ⟨n, hn⟩
  obtain ⟨k, hk⟩ := he _ hn.1
  have hj := iterate_analytic_jacobian_on f U hmap hf _ hn.1 k
  have hd := (hj.1.hasStrictDerivAt.hasDerivAt.comp z hn.2.1.hasStrictDerivAt.hasDerivAt).deriv
  refine ⟨k + n, ?_⟩
  rw [Entry, Function.iterate_add]
  exact ⟨hk, hj.1.comp hn.2.1, by rw [hd]; exact mul_ne_zero hj.2 hn.2.2⟩

theorem basin_eq_eventual_entry (f : ℂ → ℂ) (U : Set ℂ)
    (hf : ∀ z, AnalyticAt ℂ f z ∧ deriv f z ≠ 0) :
    basin f U = {z | ∃ n : ℕ, (f^[n]) z ∈ U} := by
  ext z
  constructor
  · rintro ⟨n, hn⟩; exact ⟨n, hn.1⟩
  · rintro ⟨n, hn⟩; exact ⟨n, hn, iterate_analytic_jacobian f hf z n⟩

theorem extend_abel (f φ : ℂ → ℂ) (U : Set ℂ)
    (hmap : MapsTo f U U) (habel : ∀ z ∈ U, φ (f z) = φ z + 1)
    (hf : ∀ z, AnalyticAt ℂ f z ∧ deriv f z ≠ 0)
    (z : ℂ) (hz : z ∈ basin f U) :
    f z ∈ basin f U ∧ extend f φ U (f z) = extend f φ U z + 1 := by
  obtain ⟨n, hn⟩ := hz
  have he : (f^[n]) (f z) = f ((f^[n]) z) := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  have hfn : Entry f U (f z) n :=
    ⟨by rw [he]; exact hmap hn.1, iterate_analytic_jacobian f hf (f z) n⟩
  refine ⟨⟨n, hfn⟩, ?_⟩
  rw [extend_eq_transport f φ U hmap habel _ n hfn,
    extend_eq_transport f φ U hmap habel _ n hn]
  dsimp only [transport]
  rw [he, habel _ hn.1]
  ring

end Kneser.FatouBasinExtension
end
