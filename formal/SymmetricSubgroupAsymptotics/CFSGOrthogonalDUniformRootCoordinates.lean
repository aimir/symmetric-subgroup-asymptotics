import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootMatrixArithmetic

/-! Primitive natural entry coordinates for every signed D root matrix,
uniformly over arbitrary commutative rings. Cartan coordinates are kept
separate in their intrinsic lattice. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootCoordinates
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDOriginalRootCandidates
variable (R : Type*) [CommRing R] (r : ℕ)
abbrev SignedRootIndex := Bool×RootIndex r
local instance : DecidableEq (SignedRootIndex r) := Classical.decEq _

def entry : SignedRootIndex r→Index r×Index r
  | (false,.inl ij)=>(.inl ij.val.1,.inl ij.val.2)
  | (true,.inl ij)=>(.inl ij.val.2,.inl ij.val.1)
  | (false,.inr ij)=>(.inl ij.val.1,.inr ij.val.2)
  | (true,.inr ij)=>(.inr ij.val.2,.inl ij.val.1)

def matrix : SignedRootIndex r→Mat R r
  | (false,.inl ij)=>CFSGOrthogonalDUniformRootMatrixArithmetic.difference R r ij.val.1 ij.val.2
  | (true,.inl ij)=>(CFSGOrthogonalDUniformRootMatrixArithmetic.difference R r ij.val.1 ij.val.2).transpose
  | (false,.inr ij)=>CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot R r ij.val.1 ij.val.2
  | (true,.inr ij)=>(CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot R r ij.val.1 ij.val.2).transpose

def coordinates : Mat R r→ₗ[R](SignedRootIndex r→R) where
  toFun M j:=M (entry r j).1 (entry r j).2
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

private def decode : Index r×Index r→Option (SignedRootIndex r)
  | (.inl i,.inl j)=>
    if hij : i.val < j.val then some (false,.inl ⟨(i,j),hij⟩)
    else if hji : j.val < i.val then some (true,.inl ⟨(j,i),hji⟩) else none
  | (.inl i,.inr j)=>
    if hij : i.val < j.val then some (false,.inr ⟨(i,j),hij⟩) else none
  | (.inr i,.inl j)=>
    if hji : j.val < i.val then some (true,.inr ⟨(j,i),hji⟩) else none
  | (.inr _,.inr _)=>none

private def partner : SignedRootIndex r→Index r×Index r
  | (false,.inl ij)=>(.inr ij.val.2,.inr ij.val.1)
  | (true,.inl ij)=>(.inr ij.val.1,.inr ij.val.2)
  | (false,.inr ij)=>(.inl ij.val.2,.inr ij.val.1)
  | (true,.inr ij)=>(.inr ij.val.1,.inl ij.val.2)

private theorem decode_entry (j : SignedRootIndex r) : decode r (entry r j)=some j := by
  rcases j with ⟨neg,ij | ij⟩ <;> cases neg <;>
    simp [entry,decode,ij.property,not_lt_of_ge ij.property.le]

private theorem decode_partner (j : SignedRootIndex r) : decode r (partner r j)=none := by
  rcases j with ⟨neg,ij | ij⟩ <;> cases neg <;>
    simp [partner,decode,not_lt_of_ge ij.property.le]

private theorem entry_injective : Function.Injective (entry r) := by
  intro j k h
  have hd:=congrArg (decode r) h
  rw [decode_entry,decode_entry] at hd
  exact Option.some.inj hd

private theorem entry_ne_partner (j k : SignedRootIndex r) : entry r k≠partner r j := by
  intro h
  have hd:=congrArg (decode r) h
  rw [decode_entry,decode_partner] at hd
  cases hd

private theorem matrix_formula (j : SignedRootIndex r) :
    matrix R r j=Matrix.single (entry r j).1 (entry r j).2 1-
      Matrix.single (partner r j).1 (partner r j).2 1 := by
  rcases j with ⟨neg,ij | ij⟩ <;> cases neg <;>
    simp [matrix,entry,partner,CFSGOrthogonalDUniformRootMatrixArithmetic.difference,
      CFSGOrthogonalDUniformRootMatrixArithmetic.sumRoot,Matrix.transpose_sub,Matrix.transpose_single]

theorem coordinates_matrix (j : SignedRootIndex r) :
    coordinates R r (matrix R r j)=Pi.single j 1 := by
  funext k
  change matrix R r j (entry r k).1 (entry r k).2=(Pi.single j 1 : SignedRootIndex r→R) k
  rw [matrix_formula,Matrix.sub_apply]
  have hp : ¬((partner r j).1=(entry r k).1 ∧ (partner r j).2=(entry r k).2) := by
    intro h
    exact entry_ne_partner r j k (Prod.ext h.1 h.2).symm
  rw [Matrix.single_apply_of_ne _ _ _ _ _ hp,sub_zero]
  by_cases h : j=k
  · subst k
    rw [Matrix.single_apply_same]
    simp only [Pi.single_apply,if_true]
  · have he : entry r j≠entry r k:=fun he=>h (entry_injective r he)
    have hp' : ¬((entry r j).1=(entry r k).1 ∧ (entry r j).2=(entry r k).2) :=
      fun he'=>he (Prod.ext he'.1 he'.2)
    rw [Matrix.single_apply_of_ne _ _ _ _ _ hp']
    simp only [Pi.single_apply,h,Ne.symm h,if_false]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDUniformRootCoordinates
