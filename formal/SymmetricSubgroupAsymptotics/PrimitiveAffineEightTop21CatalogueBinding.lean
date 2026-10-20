import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28TopCertificate

/-! Selected retained top21 / TransGrp 3.6.5 entry (8,37).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop21CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 3, 4, 5, 7, 6, 0] : Array (Fin 8))[x.val]!
  invFun x := (#[7, 0, 1, 2, 3, 4, 6, 5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 3, 5, 0, 2, 4, 6, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[3, 0, 4, 1, 5, 2, 6, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[5, 2, 1, 4, 3, 0, 7, 6] : Array (Fin 8))[x.val]!
  invFun x := (#[5, 2, 1, 4, 3, 0, 7, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then catalogueGenerator0 else if j.val = 1 then catalogueGenerator1 else catalogueGenerator2

def catalogueAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 6, 3, 4, 2, 1, 7, 5] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 5, 4, 2, 3, 7, 1, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .mul (.inv (.generator 1)) (.mul (.generator 0) (.mul (.generator 2) (.inv (.generator 0)))) else if j.val = 1 then .mul (.generator 1) (.mul (.generator 0) (.mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.generator 1))))) else .generator 2

private def backwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .mul (.inv (.generator 0)) (.mul (.generator 2) (.mul (.generator 0) (.generator 1))) else if j.val = 1 then .mul (.generator 0) (.mul (.generator 1) (.mul (.generator 0) (.mul (.generator 2) (.mul (.inv (.generator 0)) (.generator 1))))) else .generator 2

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    PrimitiveAffineEightFrameRow28TopCertificate.generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range PrimitiveAffineEightFrameRow28TopCertificate.generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop21CatalogueBinding
end
