import Kneser.FourierSewingSeam

/-!
Exact analytic gluing of the same Fourier sewing maps.  The hypotheses
on R and S are genuine coordinate holomorphy, their transition identity,
the imaginary period of R, and their Abel equations.  No glued map or
uniformization identity is assumed.
-/

set_option autoImplicit false
noncomputable section

namespace Kneser.FourierSewing

open Set Filter Metric
open scoped Topology Classical
open Kneser.WeightedFourier

def upperMap (H : ℝ) (P : Space) (t₀ z : ℂ) : ℂ := z + t₀ + evaluate H P z

theorem upperMap_translation (H : ℝ) (P : Space) (t₀ z : ℂ) :
    upperMap H P t₀ (z + 1) = upperMap H P t₀ z + 1 := by
  unfold upperMap
  rw [evaluate_periodic]
  ring

def gluedSewing (H h : ℝ) (Q P : Space) (t₀ : ℂ) (R S : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z.im < 0 then S (lowerMap H Q z)
  else R (upperMap H P t₀ z - (h : ℂ) * Complex.I)

theorem lowerMap_im_le (H ρ : ℝ) (Q : Space) (hQ : Q ∈ Negative)
    (hQnorm : ‖Q‖ ≤ ρ) (z : ℂ) (hz : z.im ≤ H) :
    (lowerMap H Q z).im ≤ z.im + ρ := by
  have hn := (norm_evaluate_negative_le H Q hQ z hz).trans hQnorm
  have hi := (le_abs_self (evaluate H Q z).im).trans
    ((Complex.abs_im_le_norm _).trans hn)
  simpa only [lowerMap, Complex.add_im] using add_le_add le_rfl hi

theorem upperMap_im_ge (H ρ : ℝ) (P : Space)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (hPnorm : ‖P‖ ≤ ρ)
    (t₀ z : ℂ) (hz : 0 ≤ H + z.im) :
    z.im + t₀.im - ρ ≤ (upperMap H P t₀ z).im := by
  have hn := (norm_evaluate_positive_le H P hP z hz).trans hPnorm
  have hi := (Complex.abs_im_le_norm _).trans hn
  have hl := (neg_le_of_abs_le hi)
  simp only [upperMap, Complex.add_im]
  linarith

theorem exact_gluing_identity (H h ρ : ℝ) (Q P : Space)
    (hQ : Q ∈ Negative) (hQnorm : ‖Q‖ ≤ ρ)
    (t₀ : ℂ) (t : ℤ → ℂ) (T R S : ℂ → ℂ)
    (hsew : ∀ z : ℂ, |z.im| ≤ H →
      lowerMap H Q z + t₀ + periodicFunction t (lowerMap H Q z) = upperMap H P t₀ z)
    (hT : ∀ w : ℂ, |w.im| ≤ H + ρ → T w = w + t₀ + periodicFunction t w)
    (htransition : ∀ w : ℂ, |w.im| ≤ H + ρ → R (T w) = S w)
    (hperiod : ∀ w : ℂ, R (w - (h : ℂ) * Complex.I) = R w)
    (z : ℂ) (hz : |z.im| ≤ H) :
    R (upperMap H P t₀ z - (h : ℂ) * Complex.I) = S (lowerMap H Q z) := by
  have heval := (norm_evaluate_negative_le H Q hQ z (le_abs_self z.im |>.trans hz)).trans hQnorm
  have hw : |(lowerMap H Q z).im| ≤ H + ρ := by
    calc
      _ = |z.im + (evaluate H Q z).im| := rfl
      _ ≤ |z.im| + |(evaluate H Q z).im| := abs_add_le _ _
      _ ≤ H + ρ := add_le_add hz ((Complex.abs_im_le_norm _).trans heval)
  have hid : T (lowerMap H Q z) = upperMap H P t₀ z :=
    (hT _ hw).trans (hsew z hz)
  rw [hperiod, ← hid]
  exact htransition _ hw

theorem gluedSewing_eq_lower (H h : ℝ) (hH : 0 < H) (Q P : Space)
    (t₀ : ℂ) (R S : ℂ → ℂ)
    (hglue : ∀ z : ℂ, |z.im| ≤ H →
      R (upperMap H P t₀ z - (h : ℂ) * Complex.I) = S (lowerMap H Q z))
    (z : ℂ) (hz : z.im < H) :
    gluedSewing H h Q P t₀ R S z = S (lowerMap H Q z) := by
  unfold gluedSewing
  split_ifs with hc
  · rfl
  · exact hglue z (by rw [abs_of_nonneg (by linarith : 0 ≤ z.im)]; exact hz.le)

theorem gluedSewing_eq_upper (H h : ℝ) (hH : 0 < H) (Q P : Space)
    (t₀ : ℂ) (R S : ℂ → ℂ)
    (hglue : ∀ z : ℂ, |z.im| ≤ H →
      R (upperMap H P t₀ z - (h : ℂ) * Complex.I) = S (lowerMap H Q z))
    (z : ℂ) (hz : -H < z.im) :
    gluedSewing H h Q P t₀ R S z = R (upperMap H P t₀ z - (h : ℂ) * Complex.I) := by
  unfold gluedSewing
  split_ifs with hc
  · exact (hglue z (by rw [abs_of_neg hc]; linarith)).symm
  · rfl

theorem differentiable_gluedSewing (H h ρ : ℝ) (hH : 0 < H) (Q P : Space)
    (hQ : Q ∈ Negative) (hQnorm : ‖Q‖ ≤ ρ)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (hPnorm : ‖P‖ ≤ ρ)
    (t₀ : ℂ) (R S : ℂ → ℂ)
    (hS : DifferentiableOn ℂ S {w : ℂ | w.im < H + ρ})
    (hR : DifferentiableOn ℂ R {w : ℂ | -H + t₀.im - h - ρ < w.im})
    (hglue : ∀ z : ℂ, |z.im| ≤ H →
      R (upperMap H P t₀ z - (h : ℂ) * Complex.I) = S (lowerMap H Q z)) :
    Differentiable ℂ (gluedSewing H h Q P t₀ R S) := by
  have hlower : DifferentiableOn ℂ (lowerMap H Q) {z : ℂ | z.im < H} :=
    differentiableOn_id.add (differentiableOn_evaluate_negative H Q hQ)
  have hlmap : MapsTo (lowerMap H Q) {z : ℂ | z.im < H} {w : ℂ | w.im < H + ρ} := by
    intro z hz
    change z.im < H at hz
    have hh := lowerMap_im_le H ρ Q hQ hQnorm z hz.le
    change (lowerMap H Q z).im < H + ρ
    linarith
  have hupper : DifferentiableOn ℂ (fun z => upperMap H P t₀ z - (h : ℂ) * Complex.I)
      {z : ℂ | -H < z.im} := by
    have hp := (differentiableOn_evaluate_positive H P hP).mono
      (show {z : ℂ | -H < z.im} ⊆ {z : ℂ | 0 < H + z.im} from fun z hz => by dsimp at *; linarith)
    exact ((differentiableOn_id.add (differentiableOn_const t₀)).add hp).sub
      (differentiableOn_const ((h : ℂ) * Complex.I))
  have humap : MapsTo (fun z => upperMap H P t₀ z - (h : ℂ) * Complex.I)
      {z : ℂ | -H < z.im} {w : ℂ | -H + t₀.im - h - ρ < w.im} := by
    intro z hz
    change -H < z.im at hz
    have hh := upperMap_im_ge H ρ P hP hPnorm t₀ z (by linarith)
    change -H + t₀.im - h - ρ < (upperMap H P t₀ z - (h : ℂ) * Complex.I).im
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    linarith
  have hlowcomp := (hS.comp hlower hlmap).congr
    (fun z hz => gluedSewing_eq_lower H h hH Q P t₀ R S hglue z hz)
  have hucomp := (hR.comp hupper humap).congr
    (fun z hz => gluedSewing_eq_upper H h hH Q P t₀ R S hglue z hz)
  apply differentiable_of_differentiableOn_union_of_isOpen hlowcomp hucomp
  · ext z
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    by_cases hz : z.im < H
    · exact Or.inl hz
    · exact Or.inr (by linarith)
  · exact isOpen_lt Complex.continuous_im continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_im

theorem gluedSewing_abel (H h ρ : ℝ) (hH : 0 < H) (Q P : Space)
    (hQ : Q ∈ Negative) (hQnorm : ‖Q‖ ≤ ρ)
    (hP : ∀ n : ℤ, n < 0 → P n = 0) (hPnorm : ‖P‖ ≤ ρ)
    (t₀ : ℂ) (R S f : ℂ → ℂ)
    (hSabel : ∀ w : ℂ, w.im < H + ρ → S (w + 1) = f (S w))
    (hRabel : ∀ w : ℂ, -H + t₀.im - h - ρ < w.im → R (w + 1) = f (R w))
    (z : ℂ) :
    gluedSewing H h Q P t₀ R S (z + 1) = f (gluedSewing H h Q P t₀ R S z) := by
  unfold gluedSewing
  simp only [Complex.add_im, Complex.one_im, add_zero]
  split_ifs with hc
  · rw [lowerMap_translation]
    apply hSabel
    have hh := lowerMap_im_le H ρ Q hQ hQnorm z (by linarith)
    linarith
  · rw [upperMap_translation, show upperMap H P t₀ z + 1 - (h : ℂ) * Complex.I =
      (upperMap H P t₀ z - (h : ℂ) * Complex.I) + 1 by ring]
    apply hRabel
    have hh := upperMap_im_ge H ρ P hP hPnorm t₀ z (by linarith)
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    linarith

theorem normalized_gluedSewing_upper (H h : ℝ) (hH : 0 < H) (Q P : Space)
    (t₀ ζ : ℂ) (R S : ℂ → ℂ)
    (hglue : ∀ z : ℂ, |z.im| ≤ H →
      R (upperMap H P t₀ z - (h : ℂ) * Complex.I) = S (lowerMap H Q z))
    (z : ℂ) (hz : -H < (normalizingCentre h t₀ + ζ + z).im) :
    gluedSewing H h Q P t₀ R S (normalizingCentre h t₀ + ζ + z) =
      R (sewnCoordinate H h P t₀ ζ z) := by
  exact gluedSewing_eq_upper H h hH Q P t₀ R S hglue _ hz

theorem normalized_gluedSewing_zero (H h : ℝ) (hH : 0 < H) (Q P : Space)
    (t₀ ζ : ℂ) (R S : ℂ → ℂ)
    (hglue : ∀ z : ℂ, |z.im| ≤ H →
      R (upperMap H P t₀ z - (h : ℂ) * Complex.I) = S (lowerMap H Q z))
    (hroot : normalizingCentre h t₀ + ζ + evaluate H P (normalizingCentre h t₀ + ζ) =
      normalizingCentre h t₀)
    (hpoint : -H < (normalizingCentre h t₀ + ζ).im) :
    gluedSewing H h Q P t₀ R S (normalizingCentre h t₀ + ζ) = R 0 := by
  have hh := normalized_gluedSewing_upper H h hH Q P t₀ ζ R S hglue 0 (by simpa using hpoint)
  simpa only [add_zero, sewnCoordinate_zero H h P t₀ ζ hroot] using hh

end Kneser.FourierSewing

end
