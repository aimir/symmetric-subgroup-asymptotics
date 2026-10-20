import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-! Selected exact binding to PrimGrp3.4.4 PrimitiveGroup(16,3).
The primary's bounded selected pilot returned these canonical arrays,
the identity point conjugator, and singleton words in both directions.
Every finite equality below is independently kernel checked. This is
one action binding, not a catalogue completeness theorem. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop3CatalogueBinding
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private def catalogueGenerator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,9,1,8,2,11,3,10,4,13,5,12,6,15,7,14] : Array (Fin 16))[x.val]!
  invFun x := (#[0,2,4,6,8,10,12,14,3,1,7,5,11,9,15,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  invFun x := (#[1,0,3,2,5,4,7,6,9,8,11,10,13,12,15,14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators : Fin 2 → Equiv.Perm (Fin 16) :=
  ![catalogueGenerator0, catalogueGenerator1]

def catalogueAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 16) := 1

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    DegreeTwoPrimitiveSixteenInterfaces.row3Generators catalogueGenerators where
  forward := {
    words := fun j => .generator j
    equations := by
      intro j
      fin_cases j <;> ext x <;> revert x <;> decide +kernel }
  backward := {
    words := fun j => .generator j
    equations := by
      intro j
      fin_cases j <;> ext x <;> revert x <;> decide +kernel }

theorem literal_conjugated_eq :
    MulAut.conj conjugator • DegreeTwoPrimitiveSixteenInterfaces.Row3Top =
      catalogueAction :=
  certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop3CatalogueBinding
end
