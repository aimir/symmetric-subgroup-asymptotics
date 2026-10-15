import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-! Selected retained top7 / PrimGrp 3.4.4 entry (16,7).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop7CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 1, 2, 12, 15, 13, 14, 4, 7, 5, 6, 8, 11, 9, 10] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 3, 1, 8, 10, 11, 9, 12, 14, 15, 13, 4, 6, 7, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 1, 4, 11, 14, 2, 7, 8, 13, 3, 6, 9, 12] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 4, 8, 12, 5, 1, 13, 9, 10, 14, 2, 6, 15, 11, 7, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 5, 10, 15, 4, 1, 14, 11, 8, 13, 2, 7, 12, 9, 6, 3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 3, 2, 1, 12, 15, 14, 13, 8, 11, 10, 9, 4, 7, 6, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  invFun x := (#[1, 0, 3, 2, 5, 4, 7, 6, 9, 8, 11, 10, 13, 12, 15, 14] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 5) : Equiv.Perm (Fin 16) :=
  if j.val = 0 then catalogueGenerator0 else if j.val = 1 then catalogueGenerator1 else if j.val = 2 then catalogueGenerator2 else if j.val = 3 then catalogueGenerator3 else catalogueGenerator4

def catalogueAction : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 5) : FiniteGeneratorWord (Fin 5) :=
  if j.val = 0 then .generator 0 else if j.val = 1 then .generator 1 else if j.val = 2 then .generator 2 else if j.val = 3 then .generator 3 else .generator 4

private def backwardWord (j : Fin 5) : FiniteGeneratorWord (Fin 5) :=
  if j.val = 0 then .generator 0 else if j.val = 1 then .generator 1 else if j.val = 2 then .generator 2 else if j.val = 3 then .generator 3 else .generator 4

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row7Generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row7Generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop7CatalogueBinding
end
