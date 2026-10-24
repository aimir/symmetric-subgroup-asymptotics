import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.GroupTheory.Coset.Card

/-! A genuine faithful finite-dimensional representation gives actual
group-order divisibility into GL, via its unit lift and a real basis.
No order-only recognition or guessed matrix action is involved. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FaithfulFiniteLinearRepresentationOrder

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (rho : Representation k G V)

def matrixHom : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank k V)) k :=
  (Matrix.GeneralLinearGroup.toLin' (Module.finBasis k V)).symm.toMonoidHom.comp
    rho.toHomUnits

theorem matrixHom_injective (hrho : Function.Injective rho) :
    Function.Injective (matrixHom rho) := by
  intro a b hab
  apply hrho
  have hu : rho.toHomUnits a = rho.toHomUnits b :=
    (Matrix.GeneralLinearGroup.toLin' (Module.finBasis k V)).symm.injective hab
  exact congrArg Units.val hu

theorem card_dvd_matrix_GL (hrho : Function.Injective rho) :
    Nat.card G ∣ Nat.card (Matrix.GeneralLinearGroup (Fin (Module.finrank k V)) k) :=
  Subgroup.card_dvd_of_injective (matrixHom rho) (matrixHom_injective rho hrho)

theorem card_dvd_GL_order [Finite k] (hrho : Function.Injective rho) :
    Nat.card G ∣ ∏ i : Fin (Module.finrank k V),
      (Nat.card k ^ Module.finrank k V - Nat.card k ^ (i : ℕ)) := by
  letI : Fintype k := Fintype.ofFinite k
  simpa only [Matrix.card_GL_field, Fintype.card_eq_nat_card] using
    card_dvd_matrix_GL rho hrho

end SymmetricSubgroupAsymptotics.FaithfulFiniteLinearRepresentationOrder
