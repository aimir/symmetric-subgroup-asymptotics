import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! The complete original pair action as an affine graph.

Every original element retains both its actual top permutation and its
full translation vector. The quotient of that vector by the literal
correlated kernel is a cocycle on the actual top range. The graph-fibre
identity reconstructs every original element, without a split-extension
premise or a replacement of the correlated kernel by all flips.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

theorem offset_mul (u v : U) (i : I) :
    F.offset (u*v) i=F.offset v i+F.offset u (F.top v i) := by
  change (F.frame.symm ((u : Equiv.Perm X)
    ((v : Equiv.Perm X) (F.frame (i,0))))).2=_
  rw [F.action_frame,F.action_coordinates]
  simp only [zero_add]

/-- Translation in the destination coordinate, so multiplication uses
the original left permutation action on functions. -/
def affineTranslation (u : U) : I → ZMod 2 :=
  fun i => F.offset u ((F.top u)⁻¹ i)

theorem affine_action_frame (u : U) (i : I) (b : ZMod 2) :
    (u : Equiv.Perm X) (F.frame (i,b))=
      F.frame (F.top u i,b+F.affineTranslation u (F.top u i)) := by
  rw [F.action_frame]
  simp only [affineTranslation,Equiv.Perm.inv_def,Equiv.symm_apply_apply]

theorem affineTranslation_one : F.affineTranslation 1=0 := by
  funext i
  simp only [affineTranslation,map_one,offset]
  change (F.frame.symm (F.frame (i,0))).2=0
  rw [F.frame.symm_apply_apply]

theorem affineTranslation_mul (u v : U) :
    F.affineTranslation (u*v)=
      permutationFunctionRepresentation (ZMod 2) F.top.range I
        (F.top.rangeRestrict u) (F.affineTranslation v)+F.affineTranslation u := by
  funext i
  change F.offset (u*v) ((F.top (u*v))⁻¹ i)=
    F.offset v ((F.top v)⁻¹ ((F.top u)⁻¹ i))+F.offset u ((F.top u)⁻¹ i)
  rw [F.offset_mul,map_mul,mul_inv_rev]
  simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.apply_symm_apply]

theorem affineTranslation_kernel (k : F.top.ker) :
    F.affineTranslation (k:U)=F.bits k := by
  funext i
  change F.offset (k:U) ((F.top (k:U))⁻¹ i)=F.bits k i
  rw [k.property]
  rfl

theorem affineTranslation_kernel_mul (k : F.top.ker) (u : U) :
    F.affineTranslation ((k:U)*u)=F.bits k+F.affineTranslation u := by
  rw [F.affineTranslation_mul,F.affineTranslation_kernel]
  have hk : F.top.rangeRestrict (k:U)=1 := Subtype.ext k.property
  rw [hk,map_one]
  change F.affineTranslation u+F.bits k=F.bits k+F.affineTranslation u
  exact add_comm _ _

/-- Original translations on a common top fibre differ by an actual
kernel vector, not by an arbitrary ambient flip. -/
theorem affineTranslation_sub_mem_kernelSpace (u v : U)
    (h : F.top u=F.top v) : F.affineTranslation u-F.affineTranslation v∈F.kernelSpace := by
  let k : F.top.ker := ⟨u*v⁻¹,by
    change F.top (u*v⁻¹)=1
    rw [map_mul,map_inv,h,mul_inv_cancel]⟩
  have he := F.affineTranslation_kernel_mul k v
  have hkv : (k:U)*v=u := by dsimp [k]; group
  rw [hkv] at he
  have hd : F.affineTranslation u-F.affineTranslation v=F.bits k := by
    rw [he,add_sub_cancel_right]
  rw [hd]
  exact ⟨Additive.ofMul k,rfl⟩

/-- The original point action is completely recovered from these two
coordinates. In particular no original lifts are identified here. -/
theorem affineCoordinates_injective :
    Function.Injective (fun u : U => (F.top.rangeRestrict u,F.affineTranslation u)) := by
  intro u v he
  have ht : F.top u=F.top v := congrArg Subtype.val (congrArg Prod.fst he)
  have hs : F.affineTranslation u=F.affineTranslation v := congrArg Prod.snd he
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  rw [F.affine_action_frame,F.affine_action_frame,ht,hs]

/-- The actual quotient of the original permutation module by the full
correlated kernel, with its original top-range action. -/
def affineQuotientRepresentation :
    Representation (ZMod 2) F.top.range ((I → ZMod 2) ⧸ F.kernelSpace) :=
  (permutationFunctionRepresentation (ZMod 2) F.top.range I).quotient F.kernelSpace
    (fun t => F.kernelTopPermutationSubrepresentation.apply_mem_toSubmodule t)

/-- An auxiliary lift is selected once per actual top element. The class
below is proved independent of this lift. -/
def affineTopLift (t : F.top.range) : U :=
  (F.top.rangeRestrict_surjective t).choose

theorem affineTopLift_top (t : F.top.range) :
    F.top.rangeRestrict (F.affineTopLift t)=t :=
  (F.top.rangeRestrict_surjective t).choose_spec

def affineClass (t : F.top.range) : (I → ZMod 2) ⧸ F.kernelSpace :=
  F.kernelSpace.mkQ (F.affineTranslation (F.affineTopLift t))

theorem affineClass_top (u : U) :
    F.affineClass (F.top.rangeRestrict u)=F.kernelSpace.mkQ (F.affineTranslation u) := by
  apply (Submodule.Quotient.eq F.kernelSpace).mpr
  apply F.affineTranslation_sub_mem_kernelSpace
  exact congrArg Subtype.val (F.affineTopLift_top (F.top.rangeRestrict u))

theorem affineClass_mul (t s : F.top.range) :
    F.affineClass (t*s)=F.affineQuotientRepresentation t (F.affineClass s)+F.affineClass t := by
  obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
  obtain ⟨v,rfl⟩ := F.top.rangeRestrict_surjective s
  rw [← map_mul,F.affineClass_top,F.affineClass_top,F.affineClass_top,
    F.affineTranslation_mul,map_add]
  rfl

/-- The literal original graph defines an actual first cocycle. -/
def affineCocycle : groupCohomology.cocycles₁ (Rep.of F.affineQuotientRepresentation) :=
  ⟨F.affineClass,(groupCohomology.mem_cocycles₁_iff _).mpr F.affineClass_mul⟩

/-- Exact reconstruction of the whole original group in affine
coordinates. The reverse implication uses an actual original kernel
lift, so all correlations and all original group elements are retained. -/
theorem affine_graph_fibre (t : F.top.range) (a : I → ZMod 2) :
    (∃ u : U,F.top.rangeRestrict u=t ∧ F.affineTranslation u=a) ↔
      F.kernelSpace.mkQ a=F.affineClass t := by
  constructor
  · rintro ⟨u,rfl,rfl⟩
    exact (F.affineClass_top u).symm
  · intro ha
    let v := F.affineTopLift t
    have hv : F.top.rangeRestrict v=t := F.affineTopLift_top t
    have hd : a-F.affineTranslation v∈F.kernelSpace :=
      (Submodule.Quotient.eq F.kernelSpace).mp ha
    obtain ⟨k,hk⟩ := hd
    change F.bits k.toMul=a-F.affineTranslation v at hk
    refine ⟨(k.toMul:U)*v,?_,?_⟩
    · rw [map_mul]
      have he : F.top.rangeRestrict (k.toMul:U)=1 := Subtype.ext k.toMul.property
      rw [he,one_mul,hv]
    · rw [F.affineTranslation_kernel_mul,hk,sub_add_cancel]

/-- A true equivalence with the retained graph, including every original
lift over every actual top element. -/
def affineGraphEquiv : U ≃
    {p : F.top.range × (I → ZMod 2) // F.kernelSpace.mkQ p.2=F.affineClass p.1} :=
  Equiv.ofBijective
    (fun u => ⟨(F.top.rangeRestrict u,F.affineTranslation u),(F.affineClass_top u).symm⟩)
    ⟨fun u v h => F.affineCoordinates_injective (congrArg Subtype.val h),by
      rintro ⟨⟨t,a⟩,ha⟩
      obtain ⟨u,ht,hs⟩ := (F.affine_graph_fibre t a).mpr ha
      exact ⟨u,Subtype.ext (Prod.ext ht hs)⟩⟩

@[simp] theorem affineGraphEquiv_val (u : U) :
    (F.affineGraphEquiv u).val=(F.top.rangeRestrict u,F.affineTranslation u) := rfl

end SymmetricSubgroupAsymptotics.BinaryPairFrame
