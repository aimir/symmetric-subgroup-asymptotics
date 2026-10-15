import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23TopCertificate

/-! Selected retained top14 / TransGrp 3.6.5 entry (8,23).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop14CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[1, 2, 3, 4, 5, 6, 7, 0] : Array (Fin 8))[x.val]!
  invFun x := (#[7, 0, 1, 2, 3, 4, 5, 6] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2, 1, 7, 4, 6, 5, 3, 0] : Array (Fin 8))[x.val]!
  invFun x := (#[7, 1, 0, 6, 3, 5, 4, 2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then catalogueGenerator0 else catalogueGenerator1

def catalogueAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 4, 7, 3, 6, 2, 5, 1] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 7, 5, 3, 1, 6, 4, 2] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 3) : FiniteGeneratorWord (Fin 2) :=
  if j.val = 0 then .mul (.generator 0) (.mul (.generator 0) (.mul (.generator 0) (.generator 0))) else if j.val = 1 then .inv (.generator 0) else .mul (.inv (.generator 0)) (.mul (.inv (.generator 0)) (.mul (.generator 1) (.generator 0)))

private def backwardWord (j : Fin 2) : FiniteGeneratorWord (Fin 3) :=
  if j.val = 0 then .inv (.generator 1) else .mul (.inv (.generator 1)) (.mul (.inv (.generator 1)) (.mul (.generator 2) (.generator 1)))

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    PrimitiveAffineEightFrameRow23TopCertificate.generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range PrimitiveAffineEightFrameRow23TopCertificate.generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop14CatalogueBinding
end
