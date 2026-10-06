import Kneser.ReflectedHigherPreparedCoordinate
import Kneser.SharedPreparedConsistency

/-! The degree-one member of the common preparation family is exactly the
quadratic model used by the actual first-order coordinate definitions.
These are identities of the actual series, rather than an identification
of independently selected existential witnesses. -/

set_option autoImplicit false
noncomputable section

namespace Kneser.CommonQuadraticBaseline

open Kneser.ExponentialPreparedHigher Kneser.ExponentialPreparedModel
open Kneser.ExponentialModelTime Kneser.HigherPreparedModelTime
open scoped BigOperators

def first (e : Fin 2 → ℂ → ℂ) : ℂ → ℂ := e 0
def second (e : Fin 2 → ℂ → ℂ) : ℂ → ℂ := e 1

theorem correction_one (e : Fin 2 → ℂ → ℂ) (s u : ℂ) :
    correction 1 e s u = polynomialCorrection (first e) (second e) s u := by
  simp [correction, Fin.sum_univ_two, polynomialCorrection, first, second]

theorem modelTime_one (U H : ℂ → ℂ) (e : Fin 2 → ℂ → ℂ) (s u : ℂ) :
    HigherPreparedModelTime.modelTime U H 1 e s u =
      preparedModelTime U H (first e) (second e) s u := by
  rw [HigherPreparedModelTime.modelTime, preparedModelTime, correction_one]

theorem attracting_series_one (U H A B : ℂ → ℂ) (e : Fin 2 → ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (u : ℂ) (s : ℝ) :
    Kneser.PreparedDegreeCompatibility.preparedSeries U H 1 e A B Γ u s =
      Kneser.PreparedActualFirstOrder.actualPreparedCoordinate U H (first e) (second e)
        A B Γ u s := by
  simp only [Kneser.PreparedDegreeCompatibility.preparedSeries,
    Kneser.PreparedActualFirstOrder.actualPreparedCoordinate, modelTime_one]

theorem reflected_modelTime_one (U H : ℂ → ℂ) (e : Fin 2 → ℂ → ℂ) (s v : ℂ) :
    Kneser.ReflectedHigherModelTime.modelTime U H 1 e s v =
      preparedModelTime (-U) (-H) (first e) (-(second e)) s v := by
  rw [Kneser.ReflectedHigherModelTime.modelTime, modelTime_one]
  congr 1
  · funext s
    simp [first, Kneser.ReflectedHigherModelTime.reflectedCorrection]
  · funext s
    simp [second, Kneser.ReflectedHigherModelTime.reflectedCorrection]

theorem repelling_series_one (U H A B : ℂ → ℂ) (e : Fin 2 → ℂ → ℂ)
    (Γ : ℂ × ℂ → ℂ) (v : ℂ) (s : ℝ) :
    Kneser.ReflectedHigherPreparedCoordinate.preparedSeries U H 1 e A B Γ v s =
      Kneser.ReflectedPreparedFirstOrder.actualInversePreparedCoordinate
        U H (first e) (second e) A B Γ v s := by
  simp only [Kneser.ReflectedHigherPreparedCoordinate.preparedSeries,
    Kneser.ReflectedPreparedFirstOrder.actualInversePreparedCoordinate,
    reflected_modelTime_one, Kneser.ReflectedHigherPreparedCoordinate.shiftedTerm,
    Kneser.ReflectedPreparedFirstOrder.shiftedTerm]
  rfl

end Kneser.CommonQuadraticBaseline

end
