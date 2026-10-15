import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop10TopCertificate

/-! Selected retained top10 / TransGrp 3.6.5 entry (8,47).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop10CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 7, 3, 4, 5, 6, 0] : Array (Fin 8))[x.val]!
  invFun x := (#[7, 0, 1, 3, 4, 5, 6, 2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 2, 1, 3, 4, 5, 6, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 2, 1, 3, 4, 5, 6, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4, 5, 6, 7, 0, 1, 2, 3] : Array (Fin 8))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 1, 2, 3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then catalogueGenerator0 else if j.val = 1 then catalogueGenerator1 else catalogueGenerator2

def catalogueAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 1, 2, 7, 3, 4, 5, 6] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 1, 2, 4, 5, 6, 7, 3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 9) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .mul (.generator 2) (.mul (.generator 0) (.mul (.generator 1) (.mul (.generator 0) (.mul (.generator 0) (.generator 2))))) else if j.val = 1 then .mul (.generator 2) (.mul (.generator 1) (.mul (.generator 0) (.mul (.generator 0) (.mul (.generator 1) (.generator 2))))) else if j.val = 2 then .mul (.generator 2) (.mul (.generator 0) (.mul (.generator 0) (.mul (.generator 1) (.mul (.generator 0) (.mul (.generator 0) (.mul (.generator 1) (.generator 2))))))) else if j.val = 3 then .mul (.generator 0) (.mul (.generator 0) (.mul (.generator 1) (.generator 0))) else if j.val = 4 then .mul (.generator 0) (.mul (.generator 0) (.mul (.generator 1) (.mul (.generator 0) (.mul (.generator 0) (.generator 1))))) else if j.val = 5 then .mul (.generator 1) (.mul (.generator 0) (.mul (.generator 0) (.generator 1))) else if j.val = 6 then .mul (.inv (.generator 0)) (.mul (.generator 1) (.generator 0)) else if j.val = 7 then .mul (.generator 2) (.mul (.generator 0) (.mul (.generator 0) (.mul (.generator 1) (.mul (.generator 0) (.mul (.generator 0) (.generator 2)))))) else .mul (.generator 0) (.mul (.generator 2) (.inv (.generator 0)))

private def backwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 9) :=
  if j.val = 0 then .mul (.generator 6) (.inv (.generator 3)) else if j.val = 1 then .mul (.generator 5) (.mul (.generator 6) (.generator 3)) else .mul (.generator 3) (.mul (.generator 6) (.mul (.generator 7) (.mul (.generator 8) (.inv (.generator 3)))))

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    PrimitiveAffineEightFrameTop10TopCertificate.generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range PrimitiveAffineEightFrameTop10TopCertificate.generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop10CatalogueBinding
end
