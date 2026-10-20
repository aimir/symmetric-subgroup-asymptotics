import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-! Selected retained top17 / PrimGrp 3.4.4 entry (16,17).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop17CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 10, 3, 9, 1, 11, 2, 8, 4, 14, 7, 13, 5, 15, 6, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 6, 2, 8, 12, 14, 10, 7, 3, 1, 5, 15, 11, 9, 13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 13, 10, 7, 3, 14, 9, 4, 2, 15, 8, 5, 1, 12, 11, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 12, 8, 4, 7, 11, 15, 3, 10, 6, 2, 14, 13, 1, 5, 9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 3) : Equiv.Perm (Fin 16) :=
  if j.val = 0 then catalogueGenerator0 else if j.val = 1 then catalogueGenerator1 else catalogueGenerator2

def catalogueAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .generator 0 else if j.val = 1 then .generator 1 else .generator 2

private def backwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .generator 0 else if j.val = 1 then .generator 1 else .generator 2

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row17Generators catalogueGenerators where
  forward := {
    words := forwardWord
    equations := by
      intro j
      fin_cases j <;> ext x <;> revert x <;> decide +kernel }
  backward := {
    words := backwardWord
    equations := by
      intro j
      fin_cases j <;> ext x <;> revert x <;> decide +kernel }

theorem literal_conjugated_eq :
    MulAut.conj conjugator • Subgroup.closure (Set.range Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row17Generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop17CatalogueBinding
end
