import SymmetricSubgroupAsymptotics.BinaryPairMaximalSection
import Mathlib.RepresentationTheory.Invariants

/-! The original pair-coordinate exact sequence W/L -> M/L -> L,
with W the pair-constant functions. Both the original acting group and
the literal ambient subspaces are retained. No splitting is chosen. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)
    [MulAction U I] (hact : ∀ (u : U) (i : I), u • i=F.top u i)

include hact in
private theorem pairConstant_intertwine (u : U) (a : I → ZMod 2) :
    permutationFunctionRepresentation (ZMod 2) U X u (F.pairConstant a)=
      F.pairConstant (permutationFunctionRepresentation (ZMod 2) U I u a) := by
  rw [F.pairConstant_action]
  apply congrArg F.pairConstant
  funext i
  change a ((F.top u)⁻¹ i)=a (u⁻¹ • i)
  rw [hact,map_inv]

include hact in
private theorem pairSum_intertwine (u : U) (f : X → ZMod 2) :
    F.pairSum (permutationFunctionRepresentation (ZMod 2) U X u f)=
      permutationFunctionRepresentation (ZMod 2) U I u (F.pairSum f) := by
  funext i
  change f (((u⁻¹:U):Equiv.Perm X) (F.frame (i,0)))+
      f (((u⁻¹:U):Equiv.Perm X) (F.frame (i,1)))=
      f (F.frame (u⁻¹ • i,0))+f (F.frame (u⁻¹ • i,1))
  rw [F.action_frame,F.action_frame,hact]
  have hsum (b : ZMod 2) :
      f (F.frame (F.top u⁻¹ i,0+b))+f (F.frame (F.top u⁻¹ i,1+b))=
        f (F.frame (F.top u⁻¹ i,0))+f (F.frame (F.top u⁻¹ i,1)) := by
    fin_cases b
    · change f (F.frame (F.top u⁻¹ i,(0:ZMod 2)+0))+
        f (F.frame (F.top u⁻¹ i,(1:ZMod 2)+0))=_
      rw [add_zero,add_zero]
    · change f (F.frame (F.top u⁻¹ i,(0:ZMod 2)+1))+
        f (F.frame (F.top u⁻¹ i,(1:ZMod 2)+1))=_
      rw [zero_add,CharTwo.add_self_eq_zero,add_comm]
  exact hsum (F.offset u⁻¹ i)

variable (M L : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))

/-- The original L written inside M. -/
def pairSectionDenominator (F : BinaryPairFrame U I)
    (M L : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X)) :
    Submodule (ZMod 2) M.toSubmodule :=
  L.toSubmodule.comap M.toSubmodule.subtype

/-- The quotient is the actual M/L, with its original U action. -/
def pairSectionRepresentation : Representation (ZMod 2) U
    (M.toSubmodule ⧸ F.pairSectionDenominator M L) :=
  M.toRepresentation.quotient (F.pairSectionDenominator M L) (fun u m hm =>
    L.apply_mem_toSubmodule u hm)

/-- The literal L in the original pair-constant coordinates. -/
def pairImageSubrepresentation :
    Subrepresentation (permutationFunctionRepresentation (ZMod 2) U I) where
  toSubmodule := L.toSubmodule.comap F.pairConstant
  apply_mem_toSubmodule u a ha := by
    change F.pairConstant (permutationFunctionRepresentation (ZMod 2) U I u a)∈L
    rw [← F.pairConstant_intertwine hact]
    exact L.apply_mem_toSubmodule u ha

def pairImageQuotientRepresentation : Representation (ZMod 2) U
    ((I → ZMod 2) ⧸ (F.pairImageSubrepresentation hact L).toSubmodule) :=
  (permutationFunctionRepresentation (ZMod 2) U I).quotient
    (F.pairImageSubrepresentation hact L).toSubmodule
    (fun u => (F.pairImageSubrepresentation hact L).apply_mem_toSubmodule u)

variable (hW : F.pairConstant.range≤M.toSubmodule)
    (hL : L.toSubmodule≤F.pairConstant.range)
    (himage : M.toSubmodule.map F.pairDelta≤L.toSubmodule)

private def pairConstantInside : (I → ZMod 2) →ₗ[ZMod 2] M.toSubmodule :=
  F.pairConstant.codRestrict M.toSubmodule (fun a => hW ⟨a,rfl⟩)

private def pairLeftMap :
    ((I → ZMod 2) ⧸ (F.pairImageSubrepresentation hact L).toSubmodule) →ₗ[ZMod 2]
      (M.toSubmodule ⧸ F.pairSectionDenominator M L) :=
  (F.pairImageSubrepresentation hact L).toSubmodule.liftQ
    ((F.pairSectionDenominator M L).mkQ.comp (F.pairConstantInside M hW)) (by
      intro a ha
      change (F.pairSectionDenominator M L).mkQ (F.pairConstantInside M hW a)=0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ha)

private def pairSumInside : M.toSubmodule →ₗ[ZMod 2]
    (F.pairImageSubrepresentation hact L).toSubmodule where
  toFun m := ⟨F.pairSum m.1,himage ⟨m.1,m.2,rfl⟩⟩
  map_add' _ _ := Subtype.ext (map_add F.pairSum _ _)
  map_smul' _ _ := Subtype.ext (map_smul F.pairSum _ _)

private def pairRightMap :
    (M.toSubmodule ⧸ F.pairSectionDenominator M L) →ₗ[ZMod 2]
      (F.pairImageSubrepresentation hact L).toSubmodule :=
  (F.pairSectionDenominator M L).liftQ (F.pairSumInside hact M L himage) (by
    intro m hm
    apply Subtype.ext
    change F.pairSum m.1=0
    obtain ⟨a,ha⟩ := hL hm
    change F.pairConstant a=m.1 at ha
    rw [← ha,F.pairSum_pairConstant])

/-- The inclusion of W/L into the original M/L is an actual intertwiner. -/
def pairLeftIntertwiner :
    (F.pairImageQuotientRepresentation hact L).IntertwiningMap
      (F.pairSectionRepresentation M L) where
  toLinearMap := F.pairLeftMap hact M L hW
  isIntertwining' u := by
    apply LinearMap.ext
    intro a
    obtain ⟨b,rfl⟩ := (F.pairImageSubrepresentation hact L).toSubmodule.mkQ_surjective a
    change (F.pairSectionDenominator M L).mkQ
        (F.pairConstantInside M hW (permutationFunctionRepresentation (ZMod 2) U I u b))=
      (F.pairSectionDenominator M L).mkQ
        (M.toRepresentation u (F.pairConstantInside M hW b))
    apply congrArg (F.pairSectionDenominator M L).mkQ
    apply Subtype.ext
    exact (F.pairConstant_intertwine hact u b).symm

/-- The displacement map from the original quotient takes values in the
literal original image L, written in its pair coordinates. -/
def pairRightIntertwiner :
    (F.pairSectionRepresentation M L).IntertwiningMap
      (F.pairImageSubrepresentation hact L).toRepresentation where
  toLinearMap := F.pairRightMap hact M L hL himage
  isIntertwining' u := by
    apply LinearMap.ext
    intro a
    obtain ⟨m,rfl⟩ := (F.pairSectionDenominator M L).mkQ_surjective a
    apply Subtype.ext
    exact F.pairSum_intertwine hact u m.1

theorem pairLeftIntertwiner_injective :
    Function.Injective (F.pairLeftIntertwiner hact M L hW) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm ?_ bot_le
  intro a ha
  obtain ⟨b,rfl⟩ := (F.pairImageSubrepresentation hact L).toSubmodule.mkQ_surjective a
  change (F.pairImageSubrepresentation hact L).toSubmodule.mkQ b=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  change (F.pairSectionDenominator M L).mkQ (F.pairConstantInside M hW b)=0 at ha
  exact (Submodule.Quotient.mk_eq_zero (F.pairSectionDenominator M L)).mp ha

/-- Exactness is on the actual original quotient, not on a split model. -/
theorem pair_exact :
    (F.pairLeftIntertwiner hact M L hW).toLinearMap.range=
      (F.pairRightIntertwiner hact M L hL himage).toLinearMap.ker := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    obtain ⟨b,rfl⟩ := (F.pairImageSubrepresentation hact L).toSubmodule.mkQ_surjective a
    apply Subtype.ext
    exact F.pairSum_pairConstant b
  · intro a ha
    obtain ⟨m,rfl⟩ := (F.pairSectionDenominator M L).mkQ_surjective a
    have hs : F.pairSum m.1=0 := congrArg Subtype.val ha
    have hk : m.1∈F.pairDelta.ker := by
      change F.pairConstant (F.pairSum m.1)=0
      rw [hs,map_zero]
    rw [F.pairDelta_ker] at hk
    obtain ⟨b,hb⟩ := hk
    refine ⟨(F.pairImageSubrepresentation hact L).toSubmodule.mkQ b,?_⟩
    change (F.pairSectionDenominator M L).mkQ (F.pairConstantInside M hW b)=
      (F.pairSectionDenominator M L).mkQ m
    exact congrArg (F.pairSectionDenominator M L).mkQ (Subtype.ext hb)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
