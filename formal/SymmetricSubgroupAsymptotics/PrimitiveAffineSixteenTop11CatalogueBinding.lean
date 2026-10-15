import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenInterfaces

/-! Selected retained top11 / PrimGrp 3.4.4 entry (16,11).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop11CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 13, 1, 12, 2, 15, 3, 14, 8, 5, 9, 4, 10, 7, 11, 6] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 2, 4, 6, 11, 9, 15, 13, 8, 10, 12, 14, 3, 1, 7, 5] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0, 7, 13, 10, 12, 11, 1, 6, 4, 3, 9, 14, 8, 15, 5, 2] : Array (Fin 16))[x.val]!
  invFun x := (#[0, 6, 15, 9, 8, 14, 7, 1, 12, 10, 3, 5, 4, 2, 11, 13] : Array (Fin 16))[x.val]!
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
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row11Generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPrimitiveSixteenInterfaces.row11Generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenTop11CatalogueBinding
end
