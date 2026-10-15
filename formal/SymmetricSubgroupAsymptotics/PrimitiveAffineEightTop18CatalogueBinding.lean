import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightAffineLiteralTops

/-! Selected retained top18 / TransGrp 3.6.5 entry (8,25).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop18CatalogueBinding

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

def catalogueGenerators (j : Fin 4) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then catalogueGenerator0 else if j.val = 1 then catalogueGenerator1 else if j.val = 2 then catalogueGenerator2 else catalogueGenerator3

def catalogueAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 2, 5, 3, 4, 6, 1, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 6, 1, 3, 4, 2, 5, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 2) : FiniteGeneratorWord (Fin 4) :=
  if j.val = 0 then .mul (.generator 3) (.mul (.generator 3) (.generator 2)) else .generator 1

private def backwardWord (j : Fin 4) : FiniteGeneratorWord (Fin 2) :=
  if j.val = 0 then .mul (.generator 0) (.mul (.generator 1) (.mul (.inv (.generator 0)) (.generator 1))) else if j.val = 1 then .generator 1 else if j.val = 2 then .mul (.inv (.generator 0)) (.mul (.inv (.generator 0)) (.mul (.generator 1) (.mul (.generator 0) (.generator 0)))) else .mul (.generator 0) (.mul (.generator 1) (.mul (.generator 0) (.mul (.generator 0) (.generator 0))))

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top18Generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeTwoPairedEightSharedTops.top18Generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop18CatalogueBinding
end
