import SymmetricSubgroupAsymptotics.BinaryPairSplitAffineRows
import SymmetricSubgroupAsymptotics.BinaryPairInvariantAxes
import Mathlib.Tactic.Group

/-! Reorient physical bits while retaining the original group, points,
normal subgroups, actual top and correlated kernel. A physical zero-model
conjugacy becomes a zero model in this new frame on the SAME source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

def orientationEquiv (a : I → ZMod 2) : (I × ZMod 2) ≃ (I × ZMod 2) where
  toFun p := (p.1,p.2+a p.1)
  invFun p := (p.1,p.2-a p.1)
  left_inv p := Prod.ext rfl (add_sub_cancel_right p.2 (a p.1))
  right_inv p := Prod.ext rfl (sub_add_cancel p.2 (a p.1))

/-- Only the bit-zero choices change; the source subgroup is literal. -/
def reorient (a : I → ZMod 2) : BinaryPairFrame U I where
  frame := (orientationEquiv a).trans F.frame
  top := F.top
  intertwine u p := by
    change (F.frame.symm ((u : Equiv.Perm X)
      (F.frame (p.1,p.2+a p.1)))).1 = F.top u p.1
    exact F.intertwine u (p.1,p.2+a p.1)

@[simp] theorem reorient_frame (a : I → ZMod 2) (i : I) (b : ZMod 2) :
    (F.reorient a).frame (i,b) = F.frame (i,b+a i) := rfl
@[simp] theorem reorient_top (a : I → ZMod 2) : (F.reorient a).top = F.top := rfl
@[simp] theorem reorient_top_ker (a : I → ZMod 2) : (F.reorient a).top.ker = F.top.ker := rfl

/-- Original kernel bits are unaffected by a change of the pair origins. -/
@[simp] theorem reorient_bits (a : I → ZMod 2) (k : F.top.ker) :
    (F.reorient a).bits k = F.bits k := by
  funext i
  change (F.frame.symm ((k : U).val (F.frame (i,0+a i)))).2 -
    a (F.frame.symm ((k : U).val (F.frame (i,0+a i)))).1 = F.bits k i
  simp only [F.kernel_action,zero_add]
  abel

@[simp] theorem reorient_kernelSpace (a : I → ZMod 2) :
    (F.reorient a).kernelSpace = F.kernelSpace := by
  ext v
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    change F.bits b.toMul = v
    change (F.reorient a).bits b.toMul = v at hb
    simpa only [reorient_bits] using hb
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    change (F.reorient a).bits b.toMul = v
    change F.bits b.toMul = v at hb
    simpa only [reorient_bits] using hb

@[simp] theorem reorient_physicalFlip (a k : I → ZMod 2) :
    (F.reorient a).physicalFlip k = F.physicalFlip k := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := (F.reorient a).frame.surjective x
  rw [(F.reorient a).physicalFlip_apply_frame, reorient_frame, reorient_frame,
    F.physicalFlip_apply_frame]
  apply congrArg F.frame
  apply Prod.ext
  · rfl
  · abel

/-- Affine permutations in the new frame are the exact physical
conjugates of those in the previous frame. -/
theorem reorient_affinePermutation (a v : I → ZMod 2) (t : Equiv.Perm I) :
    (F.reorient a).affinePermutation t v =
      F.physicalFlip a * F.affinePermutation t v * (F.physicalFlip a)⁻¹ := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := (F.reorient a).frame.surjective x
  change (F.reorient a).affinePermutation t v ((F.reorient a).frame (i,b)) =
    F.physicalFlip a (F.affinePermutation t v
      ((F.physicalFlip a)⁻¹ ((F.reorient a).frame (i,b))))
  rw [(F.reorient a).affinePermutation_apply_frame, reorient_frame, reorient_frame,
    F.physicalFlip_inv_apply_frame, add_sub_cancel_right,
    F.affinePermutation_apply_frame, F.physicalFlip_apply_frame]

/-- Full zero models retain precisely the same original kernel/top
coordinates after changing only the pair origins. -/
theorem reorient_splitAffineAction (a : I → ZMod 2) :
    (F.reorient a).splitAffineAction =
      F.splitAffineAction.map (MulAut.conj (F.physicalFlip a)).toMonoidHom := by
  let c := (MulAut.conj (F.physicalFlip a)).toMonoidHom
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro p ⟨t,v,hv,rfl⟩
    have hv' : v ∈ F.kernelSpace := by simpa only [reorient_kernelSpace] using hv
    refine ⟨F.affinePermutation t.val v, Subgroup.subset_closure ⟨t,v,hv',rfl⟩,?_⟩
    exact (F.reorient_affinePermutation a v t.val).symm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro p ⟨t,v,hv,rfl⟩
    change c (F.affinePermutation t.val v) ∈ (F.reorient a).splitAffineAction
    change F.physicalFlip a * F.affinePermutation t.val v * (F.physicalFlip a)⁻¹ ∈ _
    rw [← F.reorient_affinePermutation]
    exact Subgroup.subset_closure ⟨t,v,by simpa only [reorient_kernelSpace] using hv,rfl⟩

theorem physicalFlip_square_eq_one (a : I → ZMod 2) :
    F.physicalFlip a * F.physicalFlip a = 1 := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
  change F.physicalFlip a (F.physicalFlip a (F.frame (i,b))) = F.frame (i,b)
  rw [F.physicalFlip_apply_frame,F.physicalFlip_apply_frame]
  apply congrArg F.frame
  apply Prod.ext
  · rfl
  · rw [add_assoc,CharTwo.add_self_eq_zero,add_zero]

/-- A proved physical zero-model conjugacy gives a zero frame for the
same original source group and all its same original normal subgroups. -/
theorem eq_reoriented_split_of_conjugate (a : I → ZMod 2)
    (hconj : U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom = F.splitAffineAction) :
    U = (F.reorient a).splitAffineAction := by
  let c := (MulAut.conj (F.physicalFlip a)).toMonoidHom
  have hinv : (F.physicalFlip a)⁻¹ = F.physicalFlip a := by
    have h := F.physicalFlip_square_eq_one a
    exact inv_eq_of_mul_eq_one_left h
  have hc : c.comp c = MonoidHom.id (Equiv.Perm X) := by
    apply MonoidHom.ext
    intro g
    change F.physicalFlip a * (F.physicalFlip a * g * (F.physicalFlip a)⁻¹) *
      (F.physicalFlip a)⁻¹ = g
    rw [hinv]
    calc
      _ = (F.physicalFlip a * F.physicalFlip a) * g *
        (F.physicalFlip a * F.physicalFlip a) := by group
      _ = g := by simp only [F.physicalFlip_square_eq_one,one_mul,mul_one]
  rw [F.reorient_splitAffineAction,← hconj,Subgroup.map_map]
  change U = U.map (c.comp c)
  rw [hc,Subgroup.map_id]

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

/-- Every original normal and its original coordinate image are retained. -/
@[simp] theorem reorient_ambientAxis (a : Fin w → ZMod 2) (N : Subgroup U) :
    (F.reorient a).ambientAxis N = F.ambientAxis N := by
  ext v
  rw [(F.reorient a).mem_ambientAxis,F.mem_ambientAxis]
  constructor
  · rintro ⟨k,hk,he⟩
    exact ⟨k,hk,by simpa only [reorient_bits] using he⟩
  · rintro ⟨k,hk,he⟩
    exact ⟨k,hk,by simpa only [reorient_bits] using he⟩

end SymmetricSubgroupAsymptotics.BinaryPairFrame
