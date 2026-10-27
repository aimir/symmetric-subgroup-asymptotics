import SymmetricSubgroupAsymptotics.CFSGSymplecticOriginalRootCandidates
import Aesop

/-! A uniform primitive matrix family and its literal entry coordinates.
The diagonal family is D_i=H_i+...+H_last, so its coordinates require NO
inverse Cartan denominator. This is a target-side calculation only. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticOriginalRootCandidates
variable (R : Type*) [CommRing R] (r : ℕ)
local instance : DecidableEq (BasisIndex r) := Classical.decEq _

def entry : BasisIndex r → Index r × Index r
  | .inl i => (.inl i,.inl i)
  | .inr (false,.inl ij) => (.inl ij.val.1,.inl ij.val.2)
  | .inr (true,.inl ij) => (.inl ij.val.2,.inl ij.val.1)
  | .inr (false,.inr (.inl i)) => (.inl i,.inr i)
  | .inr (true,.inr (.inl i)) => (.inr i,.inl i)
  | .inr (false,.inr (.inr ij)) => (.inl ij.val.1,.inr ij.val.2)
  | .inr (true,.inr (.inr ij)) => (.inr ij.val.2,.inl ij.val.1)

def matrix : BasisIndex r → Mat R r
  | .inl i => Matrix.single (.inl i) (.inl i) 1 -
      Matrix.single (.inr i) (.inr i) 1
  | .inr (false,.inl ij) => Matrix.single (.inl ij.val.1) (.inl ij.val.2) 1 -
      Matrix.single (.inr ij.val.2) (.inr ij.val.1) 1
  | .inr (true,.inl ij) => Matrix.single (.inl ij.val.2) (.inl ij.val.1) 1 -
      Matrix.single (.inr ij.val.1) (.inr ij.val.2) 1
  | .inr (false,.inr (.inl i)) => Matrix.single (.inl i) (.inr i) 1
  | .inr (true,.inr (.inl i)) => Matrix.single (.inr i) (.inl i) 1
  | .inr (false,.inr (.inr ij)) => Matrix.single (.inl ij.val.1) (.inr ij.val.2) 1 +
      Matrix.single (.inl ij.val.2) (.inr ij.val.1) 1
  | .inr (true,.inr (.inr ij)) => Matrix.single (.inr ij.val.2) (.inl ij.val.1) 1 +
      Matrix.single (.inr ij.val.1) (.inl ij.val.2) 1

def coordinates : Mat R r →ₗ[R](BasisIndex r→R) where
  toFun M j := M (entry r j).1 (entry r j).2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def decode : Index r × Index r → Option (BasisIndex r)
  | (.inl i,.inl j) =>
    if h : i=j then some (.inl i)
    else if hij : i.val < j.val then some (.inr (false,.inl ⟨(i,j),hij⟩))
    else some (.inr (true,.inl ⟨(j,i),by
      change j.val < i.val
      have hn : i.val≠j.val := fun he => h (Fin.ext he)
      omega⟩))
  | (.inl i,.inr j) =>
    if h : i=j then some (.inr (false,.inr (.inl i)))
    else if hij : i.val < j.val then some (.inr (false,.inr (.inr ⟨(i,j),hij⟩)))
    else none
  | (.inr i,.inl j) =>
    if h : i=j then some (.inr (true,.inr (.inl i)))
    else if hji : j.val < i.val then some (.inr (true,.inr (.inr ⟨(j,i),hji⟩)))
    else none
  | (.inr _,.inr _) => none

private def partner : BasisIndex r → Index r × Index r
  | .inl i => (.inr i,.inr i)
  | .inr (false,.inl ij) => (.inr ij.val.2,.inr ij.val.1)
  | .inr (true,.inl ij) => (.inr ij.val.1,.inr ij.val.2)
  | .inr (_,.inr (.inl i)) => (.inr i,.inr i)
  | .inr (false,.inr (.inr ij)) => (.inl ij.val.2,.inr ij.val.1)
  | .inr (true,.inr (.inr ij)) => (.inr ij.val.1,.inl ij.val.2)

private def extraCoefficient : BasisIndex r → R
  | .inl _ => -1
  | .inr (_,.inl _) => -1
  | .inr (_,.inr (.inl _)) => 0
  | .inr (_,.inr (.inr _)) => 1

private theorem pair_ne (ij : Pair r) : ij.val.1≠ij.val.2 := by
  intro h
  have hv:=congrArg Fin.val h
  have hp:=ij.property
  omega

private theorem decode_entry (j : BasisIndex r) : decode r (entry r j)=some j := by
  rcases j with i | ⟨neg,j⟩
  · simp [entry,decode]
  · cases neg <;> rcases j with ij | (i | ij)
    · simp [entry,decode,pair_ne r ij,ij.property]
    · simp [entry,decode]
    · simp [entry,decode,pair_ne r ij,ij.property]
    · simp [entry,decode,Ne.symm (pair_ne r ij),not_lt_of_ge ij.property.le]
    · simp [entry,decode]
    · simp [entry,decode,Ne.symm (pair_ne r ij),ij.property]

private theorem decode_partner (j : BasisIndex r) : decode r (partner r j)=none := by
  rcases j with i | ⟨neg,j⟩
  · rfl
  · cases neg <;> rcases j with ij | (i | ij)
    · rfl
    · rfl
    · simp [partner,decode,Ne.symm (pair_ne r ij),not_lt_of_ge ij.property.le]
    · rfl
    · rfl
    · simp [partner,decode,pair_ne r ij,not_lt_of_ge ij.property.le]

private theorem entry_injective : Function.Injective (entry r) := by
  intro j k h
  have hd:=congrArg (decode r) h
  rw [decode_entry,decode_entry] at hd
  exact Option.some.inj hd

private theorem entry_ne_partner (j k : BasisIndex r) : entry r k≠partner r j := by
  intro h
  have hd:=congrArg (decode r) h
  rw [decode_entry,decode_partner] at hd
  cases hd

private theorem matrix_formula (j : BasisIndex r) :
    matrix R r j=Matrix.single (entry r j).1 (entry r j).2 1+
      extraCoefficient R r j • Matrix.single (partner r j).1 (partner r j).2 1 := by
  rcases j with i | ⟨neg,j⟩
  · simp [matrix,entry,partner,extraCoefficient,sub_eq_add_neg]
  · cases neg <;> rcases j with ij | (i | ij) <;>
      simp [matrix,entry,partner,extraCoefficient,sub_eq_add_neg]

/-- Entry selection is primitive, uniformly in rank and characteristic. -/
theorem coordinates_matrix (j : BasisIndex r) :
    coordinates R r (matrix R r j)=Pi.single j 1 := by
  classical
  funext k
  change matrix R r j (entry r k).1 (entry r k).2=(Pi.single j 1 : BasisIndex r→R) k
  rw [matrix_formula,Matrix.add_apply,Matrix.smul_apply]
  have hp : ¬((partner r j).1=(entry r k).1 ∧ (partner r j).2=(entry r k).2) := by
    intro h
    exact entry_ne_partner r j k (Prod.ext h.1 h.2).symm
  rw [Matrix.single_apply_of_ne _ _ _ _ _ hp,smul_zero,add_zero]
  by_cases h : j=k
  · subst k
    rw [Matrix.single_apply_same]
    simp only [Pi.single_apply,if_true]
  · have he : entry r j≠entry r k := fun he => h (entry_injective r he)
    have hp' : ¬((entry r j).1=(entry r k).1 ∧ (entry r j).2=(entry r k).2) :=
      fun he' => he (Prod.ext he'.1 he'.2)
    rw [Matrix.single_apply_of_ne _ _ _ _ _ hp']
    simp only [Pi.single_apply,h,Ne.symm h,if_false]

end SymmetricSubgroupAsymptotics.CFSGSymplecticUniformRootCoordinates
