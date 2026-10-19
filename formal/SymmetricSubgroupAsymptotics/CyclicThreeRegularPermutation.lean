import SymmetricSubgroupAsymptotics.NaturalA4ScalarFourHead
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CyclicThreeRegularPermutation

private theorem card_three : Nat.card CyclicThree=3 := by
  rw [Nat.card_congr Multiplicative.toAdd]
  simp

private def points : CyclicThree ≃ Fin 3 := Finite.equivFinOfCardEq card_three

def representation : CyclicThree →* Equiv.Perm (Fin 3) :=
  points.permCongrHom.toMonoidHom.comp (MulAction.toPermHom CyclicThree CyclicThree)

theorem representation_injective : Function.Injective representation := by
  intro x y h
  have hh : MulAction.toPermHom CyclicThree CyclicThree x=
      MulAction.toPermHom CyclicThree CyclicThree y := points.permCongrHom.injective h
  have h1 := congrArg (fun p : Equiv.Perm CyclicThree => p 1) hh
  simpa using h1

end SymmetricSubgroupAsymptotics.CyclicThreeRegularPermutation
