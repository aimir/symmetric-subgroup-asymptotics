import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineLiteralTops

/-! Selected retained top20 / TransGrp 3.6.5 entry (8,48).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop20CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[7, 2, 1, 4, 3, 6, 5, 0] : Array (Fin 8))[x.val]!
  invFun x := (#[7, 2, 1, 4, 3, 6, 5, 0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2, 7, 0, 5, 6, 3, 4, 1] : Array (Fin 8))[x.val]!
  invFun x := (#[2, 7, 0, 5, 6, 3, 4, 1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3] : Array (Fin 8))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 5, 3, 4, 6, 2, 0, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[6, 0, 5, 2, 3, 1, 4, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator4 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 0, 5, 3, 4, 6, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[2, 0, 1, 4, 5, 3, 6, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator5 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 0, 2, 3, 5, 4, 6, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[1, 0, 2, 3, 5, 4, 6, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 6) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then catalogueGenerator0 else if j.val = 1 then catalogueGenerator1 else if j.val = 2 then catalogueGenerator2 else if j.val = 3 then catalogueGenerator3 else if j.val = 4 then catalogueGenerator4 else catalogueGenerator5

def catalogueAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 3, 2, 5, 7, 4, 1, 6] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 6, 2, 1, 5, 3, 7, 4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 6) :=
  if j.val = 0 then .mul (.generator 5) (.mul (.inv (.generator 3)) (.mul (.generator 2) (.generator 4))) else if j.val = 1 then .mul (.generator 3) (.mul (.generator 4) (.mul (.generator 3) (.mul (.generator 5) (.mul (.generator 3) (.generator 4))))) else .mul (.generator 0) (.generator 2)

private def backwardWord (j : Fin 6) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .mul (.inv (.generator 0)) (.mul (.generator 1) (.mul (.generator 2) (.mul (.generator 1) (.generator 0)))) else if j.val = 1 then .mul (.generator 1) (.mul (.generator 2) (.generator 1)) else if j.val = 2 then .mul (.generator 1) (.mul (.generator 0) (.mul (.generator 2) (.mul (.inv (.generator 0)) (.generator 1)))) else if j.val = 3 then .mul (.generator 0) (.mul (.generator 1) (.mul (.inv (.generator 0)) (.mul (.generator 2) (.mul (.inv (.generator 0)) (.mul (.generator 1) (.mul (.generator 0) (.generator 1))))))) else if j.val = 4 then .mul (.generator 0) (.mul (.generator 0) (.mul (.generator 0) (.mul (.generator 1) (.mul (.inv (.generator 0)) (.mul (.inv (.generator 0)) (.mul (.generator 2) (.generator 1))))))) else .mul (.generator 2) (.mul (.inv (.generator 0)) (.mul (.generator 1) (.mul (.generator 0) (.generator 2))))

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top20Generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top20Generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop20CatalogueBinding
end
