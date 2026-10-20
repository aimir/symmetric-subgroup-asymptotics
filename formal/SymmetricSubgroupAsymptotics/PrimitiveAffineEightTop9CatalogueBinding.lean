import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop9TopCertificate

/-! Selected retained top9 / TransGrp 3.6.5 entry (8,46).
Both actual generator inclusions are checked pointwise by the Lean kernel.
This states no catalogue completeness, frame bound, or normal bound. -/

set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop9CatalogueBinding

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
  toFun x := (#[7, 1, 2, 4, 3, 5, 6, 0] : Array (Fin 8))[x.val]!
  invFun x := (#[7, 1, 2, 4, 3, 5, 6, 0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[4, 6, 5, 7, 0, 1, 2, 3] : Array (Fin 8))[x.val]!
  invFun x := (#[4, 5, 6, 7, 0, 2, 1, 3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 4) : Equiv.Perm (Fin 8) :=
  if j.val = 0 then catalogueGenerator0 else if j.val = 1 then catalogueGenerator1 else if j.val = 2 then catalogueGenerator2 else catalogueGenerator3

def catalogueAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0, 1, 2, 7, 3, 4, 5, 6] : Array (Fin 8))[x.val]!
  invFun x := (#[0, 1, 2, 4, 5, 6, 7, 3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 8) : FiniteGeneratorWord (Fin 4) :=
  if j.val = 0 then .mul (.generator 1) (.mul (.generator 0) (.mul (.generator 3) (.generator 3))) else if j.val = 1 then .mul (.generator 3) (.mul (.generator 1) (.inv (.generator 3))) else if j.val = 2 then .mul (.generator 3) (.mul (.generator 0) (.inv (.generator 3))) else if j.val = 3 then .mul (.generator 0) (.mul (.generator 2) (.mul (.generator 0) (.mul (.generator 3) (.generator 3)))) else if j.val = 4 then .mul (.generator 1) (.generator 0) else if j.val = 5 then .mul (.inv (.generator 1)) (.mul (.generator 0) (.generator 1)) else if j.val = 6 then .mul (.generator 1) (.mul (.generator 0) (.inv (.generator 1))) else .mul (.generator 2) (.mul (.generator 1) (.mul (.generator 3) (.mul (.generator 0) (.generator 1))))

private def backwardWord (j : Fin 4) : FiniteGeneratorWord (Fin 8) :=
  if j.val = 0 then .mul (.generator 5) (.generator 6) else if j.val = 1 then .mul (.generator 6) (.generator 4) else if j.val = 2 then .mul (.generator 0) (.mul (.generator 3) (.mul (.generator 4) (.generator 5))) else .mul (.generator 3) (.mul (.generator 4) (.mul (.inv (.generator 1)) (.inv (.generator 7))))

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    PrimitiveAffineEightFrameTop9TopCertificate.generators catalogueGenerators where
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
    MulAut.conj conjugator • Subgroup.closure (Set.range PrimitiveAffineEightFrameTop9TopCertificate.generators) =
      catalogueAction := certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop9CatalogueBinding
end
