import SymmetricSubgroupAsymptotics.FiniteGeneratorEquivWordCertificate
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0TopCertificate

/-!
Exact selected binding of the retained top1/frame0 to the displayed
generators of TransGrp 3.6.5 entry TransitiveGroup(8,13).

The external selected pilot supplies only finite point arrays and words.
Every word and inverse identity below is checked by kernel reduction on
Fin 8. The final theorem proves equality under the displayed ambient
point conjugator. It asserts neither catalogue exhaustiveness nor any
frame or normal-subgroup bound.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop1CatalogueBinding

private def catalogueGenerator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,2,1,4,3,6,5,0] : Array (Fin 8))[x.val]!
  invFun x := (#[7,2,1,4,3,6,5,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  invFun x := (#[2,7,0,5,6,3,4,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator2 : Equiv.Perm (Fin 8) where
  toFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  invFun x := (#[4,5,6,7,0,1,2,3] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def catalogueGenerator3 : Equiv.Perm (Fin 8) where
  toFun x := (#[1,2,0,5,3,4,6,7] : Array (Fin 8))[x.val]!
  invFun x := (#[2,0,1,4,5,3,6,7] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def catalogueGenerators (j : Fin 4) : Equiv.Perm (Fin 8) :=
  if j.val < 2 then
    if j.val < 1 then catalogueGenerator0 else catalogueGenerator1
  else if j.val < 3 then catalogueGenerator2 else catalogueGenerator3

def catalogueAction : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure (Set.range catalogueGenerators)

def conjugator : Equiv.Perm (Fin 8) where
  toFun x := (#[0,7,1,2,5,6,4,3] : Array (Fin 8))[x.val]!
  invFun x := (#[0,2,3,7,6,4,5,1] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def forwardWord (j : Fin 4) : FiniteGeneratorWord (Fin 4) :=
  if j.val < 2 then
    if j.val < 1 then .mul (.generator 3) (.generator 1) else .generator 1
  else if j.val < 3 then .generator 0
  else .mul (.generator 0) (.mul (.generator 1) (.generator 2))

private def backwardWord (j : Fin 4) : FiniteGeneratorWord (Fin 4) :=
  if j.val < 2 then
    if j.val < 1 then .generator 2 else .generator 1
  else if j.val < 3 then .mul (.generator 1) (.mul (.generator 2) (.generator 3))
  else .mul (.generator 0) (.generator 1)

def certificate : FiniteGeneratorEquivWordCertificate (MulAut.conj conjugator)
    PrimitiveAffineEightFrameRow0TopCertificate.generators catalogueGenerators where
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

/-- The exact original retained action is conjugate to the displayed
catalogue action, with both directions certified by literal words. -/
theorem literal_conjugated_eq :
    MulAut.conj conjugator • Subgroup.closure
        (Set.range PrimitiveAffineEightFrameRow0TopCertificate.generators) =
      catalogueAction :=
  certificate.map_closure_eq

end SymmetricSubgroupAsymptotics.PrimitiveAffineEightTop1CatalogueBinding

end
