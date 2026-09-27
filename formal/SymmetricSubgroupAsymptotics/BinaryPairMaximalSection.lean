import SymmetricSubgroupAsymptotics.BinaryPairFrameEquivariance
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead
import SymmetricSubgroupAsymptotics.MaximalTrivialSection
import Mathlib.Algebra.CharP.Two

/-! Equality in the half-degree trivial-section bound for a literal
original pair involution. The kernel of its displacement is identified
with functions on the original pairs, rather than supplied as a dimension
hypothesis. The ambient correlated subspaces M and L are kept throughout. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- Functions constant on each literal original pair. -/
def pairConstant : (I → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) where
  toFun a x := a (F.frame.symm x).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pairConstant_frame (a : I → ZMod 2) (i : I) (b : ZMod 2) :
    F.pairConstant a (F.frame (i,b))=a i := by
  change a (F.frame.symm (F.frame (i,b))).1=a i
  rw [Equiv.symm_apply_apply]

theorem pairConstant_injective : Function.Injective F.pairConstant := by
  intro a b h
  funext i
  have hi := congrFun h (F.frame (i,0))
  simpa only [F.pairConstant_frame] using hi

/-- Sum along the two points of the same original pair. -/
def pairSum : (X → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) where
  toFun f i := f (F.frame (i,0))+f (F.frame (i,1))
  map_add' f g := by
    funext i
    change (f (F.frame (i,0))+g (F.frame (i,0)))+
      (f (F.frame (i,1))+g (F.frame (i,1)))=
      (f (F.frame (i,0))+f (F.frame (i,1)))+
      (g (F.frame (i,0))+g (F.frame (i,1)))
    abel
  map_smul' c f := by ext i; exact (smul_add c _ _).symm

@[simp] theorem pairSum_pairConstant (a : I → ZMod 2) :
    F.pairSum (F.pairConstant a)=0 := by
  funext i
  change F.pairConstant a (F.frame (i,0))+F.pairConstant a (F.frame (i,1))=0
  rw [F.pairConstant_frame,F.pairConstant_frame,CharTwo.add_self_eq_zero]

/-- The displacement of the all-pair flip in original coordinates. -/
def pairDelta : (X → ZMod 2) →ₗ[ZMod 2] (X → ZMod 2) :=
  F.pairConstant.comp F.pairSum

@[simp] theorem pairDelta_frame (f : X → ZMod 2) (i : I) (b : ZMod 2) :
    F.pairDelta f (F.frame (i,b))=f (F.frame (i,0))+f (F.frame (i,1)) :=
  F.pairConstant_frame (F.pairSum f) i b

theorem pairDelta_square_zero : F.pairDelta.comp F.pairDelta=0 := by
  apply LinearMap.ext
  intro f
  change F.pairConstant (F.pairSum (F.pairConstant (F.pairSum f)))=0
  rw [F.pairSum_pairConstant,map_zero]

/-- The original displacement kernel is exactly the original pair-constant
range. This is an equality of ambient subspaces, not just dimensions. -/
theorem pairDelta_ker : F.pairDelta.ker=F.pairConstant.range := by
  apply le_antisymm
  · intro f hf
    refine ⟨fun i => f (F.frame (i,0)),?_⟩
    funext x
    obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
    rw [F.pairConstant_frame]
    have hzero := congrFun (show F.pairDelta f=0 from hf) (F.frame (i,0))
    have he : f (F.frame (i,0))=f (F.frame (i,1)) :=
      CharTwo.add_eq_zero.mp (by simpa only [F.pairDelta_frame,Pi.zero_apply] using hzero)
    fin_cases b
    · rfl
    · exact he
  · rintro _ ⟨a,rfl⟩
    change F.pairConstant (F.pairSum (F.pairConstant a))=0
    rw [F.pairSum_pairConstant,map_zero]

theorem pairDelta_ker_finrank [Finite I] :
    Module.finrank (ZMod 2) F.pairDelta.ker=Nat.card I := by
  rw [F.pairDelta_ker,← (LinearEquiv.ofInjective F.pairConstant
    F.pairConstant_injective).finrank_eq,Module.finrank_pi,Nat.card_eq_fintype_card]

/-- The original top action is retained on the constant-pair coordinates. -/
theorem pairConstant_action (u : U) (a : I → ZMod 2) :
    permutationFunctionRepresentation (ZMod 2) U X u (F.pairConstant a)=
      F.pairConstant (fun i => a ((F.top u)⁻¹ i)) := by
  funext x
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  change a (F.frame.symm (((u⁻¹ : U) : Equiv.Perm X) (F.frame (i,b)))).1=_
  rw [F.intertwine,map_inv,F.pairConstant_frame]

/-- If the supplied original kernel element flips every pair, the
coordinate displacement is its literal original representation minus one. -/
theorem pairDelta_eq_original_displacement (z : F.top.ker)
    (hz : ∀ i, F.bits z i=1) :
    F.pairDelta=permutationFunctionRepresentation (ZMod 2) U X (z:U)-LinearMap.id := by
  have hinv (i : I) : F.bits z⁻¹ i=1 := by
    have hi := congrArg (fun a : Multiplicative (I → ZMod 2) => a.toAdd i)
      (F.bitsHom.map_inv z)
    change F.bits z⁻¹ i = -F.bits z i at hi
    simpa only [hz i,CharTwo.neg_eq] using hi
  apply LinearMap.ext
  intro f
  funext x
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  rw [F.pairDelta_frame]
  change _=f ((((z⁻¹ : F.top.ker):U) : Equiv.Perm X) (F.frame (i,b)))-f (F.frame (i,b))
  rw [F.kernel_action_frame,hinv]
  fin_cases b
  · change f (F.frame (i,0))+f (F.frame (i,1))=
      f (F.frame (i,(0:ZMod 2)+1))-f (F.frame (i,0))
    rw [zero_add,CharTwo.sub_eq_add,add_comm]
  · change f (F.frame (i,0))+f (F.frame (i,1))=
      f (F.frame (i,(1:ZMod 2)+1))-f (F.frame (i,1))
    rw [CharTwo.add_self_eq_zero,CharTwo.sub_eq_add]

/-- Maximal trivial sections recover all original pair-constant vectors
and the complete original preimage of L. No reachability, splitting, or
uncorrelated-kernel assumption enters the conclusion. -/
theorem maximal_pair_section [Finite X] [Finite I]
    (z : F.top.ker) (hz : ∀ i, F.bits z i=1)
    (M L : Submodule (ZMod 2) (X → ZMod 2)) (hLM : L≤M)
    (htrivial : ∀ f ∈ M,
      permutationFunctionRepresentation (ZMod 2) U X (z:U) f-f ∈ L)
    (hdim : Module.finrank (ZMod 2) (M ⧸ L.comap M.subtype)=Nat.card I) :
    F.pairConstant.range≤M ∧ L=M.map F.pairDelta ∧
      L≤F.pairConstant.range ∧ M=L.comap F.pairDelta := by
  have himage : M.map F.pairDelta≤L := by
    rintro _ ⟨f,hf,rfl⟩
    rw [F.pairDelta_eq_original_displacement z hz]
    exact htrivial f hf
  have hd : Module.finrank (ZMod 2) (M ⧸ L.comap M.subtype)=
      Module.finrank (ZMod 2) F.pairDelta.ker := by
    rw [F.pairDelta_ker_finrank]
    exact hdim
  simpa only [F.pairDelta_ker] using
    MaximalTrivialSection.eq_of_maximal_quotient_finrank_of_square_zero
      F.pairDelta M L hLM himage hd F.pairDelta_square_zero

end SymmetricSubgroupAsymptotics.BinaryPairFrame
