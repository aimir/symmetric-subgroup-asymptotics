import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow4TopCertificate

/-! Selected retained top5 / TransGrp 3.6.5 entry (8,42).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop5CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2, 7, 0, 3, 4, 5, 6, 1] : Array (Fin 8))[x.val]!
  invFun x := (#[2, 7, 0, 3, 4, 5, 6, 1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 0, 3, 4, 5, 6, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[2, 0, 1, 3, 4, 5, 6, 7] : Array (Fin 8))[x.val]!
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
  toFun x := (#[0, 7, 1, 2, 4, 6, 3, 5] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 2, 3, 6, 4, 7, 5, 1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 7) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .mul (.generator 2) (.mul (.generator 1) (.mul (.generator 0) (.generator 2))) else if j.val = 1 then .mul (.generator 2) (.mul (.generator 1) (.mul (.generator 0) (.mul (.inv (.generator 1)) (.generator 2)))) else if j.val = 2 then .mul (.generator 2) (.mul (.generator 0) (.generator 2)) else if j.val = 3 then .mul (.generator 1) (.generator 0) else if j.val = 4 then .generator 0 else if j.val = 5 then .mul (.inv (.generator 1)) (.mul (.generator 0) (.generator 1)) else .mul (.generator 0) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.mul (.generator 1) (.generator 0))))

private def backwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 7) :=
  if j.val = 0 then .generator 4 else if j.val = 1 then .mul (.generator 3) (.generator 4) else .mul (.generator 3) (.mul (.generator 6) (.inv (.generator 3)))

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    PrimitiveAffineEightFrameRow4TopCertificate.generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range PrimitiveAffineEightFrameRow4TopCertificate.generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop5CatalogueBinding
end
