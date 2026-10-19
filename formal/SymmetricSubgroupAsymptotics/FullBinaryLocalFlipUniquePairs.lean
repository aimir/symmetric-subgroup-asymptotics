import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! Independent original local flips force the unique invariant physical
pairing. This supplies the frame-independence needed to use an existential
published top realization, without strengthening its quantification. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FullBinaryLocalFlipUniquePairs

variable {I J : Type}

def localFlip (i : I) : Equiv.Perm (I × ZMod 2) where
  toFun x := (x.1,if x.1=i then x.2+1 else x.2)
  invFun x := (x.1,if x.1=i then x.2+1 else x.2)
  left_inv x := by
    rcases x with ⟨j,b⟩
    by_cases hj : j=i <;>
      simp [hj,add_assoc,show (1 : ZMod 2)+1=0 by decide]
  right_inv x := by
    rcases x with ⟨j,b⟩
    by_cases hj : j=i <;>
      simp [hj,add_assoc,show (1 : ZMod 2)+1=0 by decide]

private theorem binary_other : ∀ a b : ZMod 2,b≠a → b=a+1 := by decide +kernel

variable {V : Subgroup (Equiv.Perm (I × ZMod 2))}
  (hflip : ∀ i : I,localFlip i∈V) (R : BinaryPairFrame V J)

include hflip in
/-- A partner in another fibre would be fixed by a local flip which moves
the first point, contradicting injectivity of the original partner map. -/
theorem partner_fst (x : I × ZMod 2) : (R.partnerMap x).1=x.1 := by
  by_contra hx
  let g : V := ⟨localFlip x.1,hflip x.1⟩
  have hy : (g : Equiv.Perm (I × ZMod 2)) (R.partnerMap x)=R.partnerMap x := by
    change ((R.partnerMap x).1,
      if (R.partnerMap x).1=x.1 then (R.partnerMap x).2+1 else (R.partnerMap x).2)=R.partnerMap x
    simp only [if_neg hx,Prod.eta]
  have he : R.partnerMap ((g : Equiv.Perm (I × ZMod 2)) x)=R.partnerMap x :=
    (R.partnerMap_equivariant g x).trans hy
  have hg : (g : Equiv.Perm (I × ZMod 2)) x=x := R.partnerMap_involutive.injective he
  have hb := congrArg Prod.snd hg
  change (if x.1=x.1 then x.2+1 else x.2)=x.2 at hb
  rw [if_pos rfl] at hb
  have hn : (1 : ZMod 2)=0 := add_left_cancel (hb.trans (add_zero x.2).symm)
  norm_num at hn

include hflip in
/-- Every invariant binary frame has EXACTLY the displayed physical pairs. -/
theorem partner_eq (x : I × ZMod 2) : R.partnerMap x=(x.1,x.2+1) := by
  have hf := partner_fst hflip R x
  have hn : (R.partnerMap x).2≠x.2 := by
    intro hb
    exact R.partnerMap_ne x (Prod.ext hf hb)
  exact Prod.ext hf (binary_other x.2 (R.partnerMap x).2 hn)

end SymmetricSubgroupAsymptotics.FullBinaryLocalFlipUniquePairs
