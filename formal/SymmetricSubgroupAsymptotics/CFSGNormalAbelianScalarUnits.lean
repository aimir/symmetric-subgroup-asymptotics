import SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarKernel
import Mathlib.Data.Fintype.Units

/-! The original abelian normal subgroup embeds in the units of its
actual scalar-image field. In particular a nontrivial subgroup cannot
produce only the binary prime field. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra IsMulCommutative

namespace SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarUnits
open CFSGIsotypicCommutativeScalarField CFSGIsotypicScalarAction
  CFSGNormalAbelianScalarConjugation

variable {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal] [IsMulCommutative H]

def scalarGroupHom : H →* scalarQuotient (restriction rho H) :=
  (Ideal.Quotient.mk (RingHom.ker (restriction rho H).asAlgebraHom.toRingHom)).toMonoidHom.comp
    (MonoidAlgebra.of k H)

omit [H.Normal] in
theorem scalarGroupHom_action (h : H) :
    scalarAction (restriction rho H) (scalarGroupHom rho H h) = rho h := by
  change scalarAction (restriction rho H)
    (Ideal.Quotient.mk _ (MonoidAlgebra.of k H h)) = rho h
  rw [MonoidAlgebra.of_apply, scalarAction_mk, Representation.asAlgebraHom_single_one]
  rfl

theorem scalarGroupHom_injective (hf : Function.Injective rho) :
    Function.Injective (scalarGroupHom rho H) := by
  intro a b hab
  apply Subtype.ext
  apply hf
  have he := congrArg (scalarAction (restriction rho H)) hab
  simpa only [scalarGroupHom_action] using he

def scalarUnitHom : H →* (scalarQuotient (restriction rho H))ˣ :=
  (scalarGroupHom rho H).toHomUnits

theorem scalarUnitHom_injective (hf : Function.Injective rho) :
    Function.Injective (scalarUnitHom rho H) := by
  intro a b hab
  exact scalarGroupHom_injective rho H hf (congrArg Units.val hab)

theorem scalar_card_gt_two [Finite G] [Finite V] [Nontrivial V]
    (hf : Function.Injective rho) (hH : H ≠ ⊥)
    (hss : IsSemisimpleModule k[H] (restriction rho H).asModule)
    (hiso : IsIsotypic k[H] (restriction rho H).asModule) :
    2 < Nat.card (scalarQuotient (restriction rho H)) := by
  let tau := restriction rho H
  change 2 < Nat.card (scalarQuotient tau)
  letI : Finite tau.asModule :=
    Finite.of_injective tau.asModuleEquiv tau.asModuleEquiv.injective
  letI : Module.Finite k[H] tau.asModule := Module.Finite.of_finite
  letI : Nontrivial tau.asModule := tau.asModuleEquiv.toEquiv.nontrivial
  letI : IsSemisimpleModule k[H] tau.asModule := hss
  letI : Field (scalarQuotient tau) := scalarField tau hiso
  letI : Finite (scalarQuotient tau) := scalarQuotient_finite tau
  letI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hH
  have hcard : 1 < Nat.card H := Finite.one_lt_card (α := H)
  have hle := Nat.card_le_card_of_injective (scalarUnitHom rho H)
    (scalarUnitHom_injective rho H hf)
  have hu : Nat.card ((scalarQuotient tau)ˣ) = Nat.card (scalarQuotient tau) - 1 :=
    Nat.card_units (scalarQuotient tau)
  change Nat.card H ≤ Nat.card ((scalarQuotient tau)ˣ) at hle
  rw [hu] at hle
  omega

end SymmetricSubgroupAsymptotics.CFSGNormalAbelianScalarUnits
