import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1TopCertificate

/-! Selected retained top2 / TransGrp 3.6.5 entry (8,14).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop2CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[2, 7, 0, 5, 6, 3, 4, 1] : Array (Fin 8))[x.val]!
  invFun x := (#[2, 7, 0, 5, 6, 3, 4, 1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 0, 3, 5, 6, 4, 7] : Array (Fin 8))[x.val]!
  invFun x := (#[2, 0, 1, 3, 6, 4, 5, 7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[3, 5, 6, 0, 7, 1, 2, 4] : Array (Fin 8))[x.val]!
  invFun x := (#[3, 5, 6, 0, 7, 1, 2, 4] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 3) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then catalogueGenerator0 else if j.val = 1 then catalogueGenerator1 else catalogueGenerator2

def catalogueAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 7, 1, 2, 3, 4, 5, 6] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 2, 3, 4, 5, 6, 7, 1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 4) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .mul (.generator 1) (.generator 0) else if j.val = 1 then .generator 0 else if j.val = 2 then .mul (.inv (.generator 1)) (.mul (.generator 0) (.generator 1)) else .generator 2

private def backwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 4) :=
  if j.val = 0 then .generator 1 else if j.val = 1 then .mul (.generator 0) (.generator 1) else .generator 3

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    PrimitiveAffineEightFrameRow1TopCertificate.generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range PrimitiveAffineEightFrameRow1TopCertificate.generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop2CatalogueBinding
end
