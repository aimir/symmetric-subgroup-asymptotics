import SymmetricSubgroupAsymptotics.BinaryPairFrames

/-! The literal pair coordinates intertwine original conjugation with
the actual top permutation action. The offsets of an arbitrary original
element cancel; correlations in the kernel flip space remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X I : Type*} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

def offset (u : U) (i : I) : ZMod 2 :=
  (F.frame.symm ((u : Equiv.Perm X) (F.frame (i,0)))).2

theorem action_coordinates (u : U) (i : I) (b : ZMod 2) :
    F.frame.symm ((u : Equiv.Perm X) (F.frame (i,b)))=
      (F.top u i,b+F.offset u i) := by
  apply Prod.ext
  · exact F.intertwine u (i,b)
  · apply binary_injective_translate
      (fun t=>(F.frame.symm ((u:Equiv.Perm X) (F.frame (i,t)))).2)
    intro a b hab
    have he : F.frame.symm ((u:Equiv.Perm X) (F.frame (i,a)))=
        F.frame.symm ((u:Equiv.Perm X) (F.frame (i,b))) :=
      Prod.ext ((F.intertwine u (i,a)).trans (F.intertwine u (i,b)).symm) hab
    exact congrArg Prod.snd (F.frame.injective
      ((u:Equiv.Perm X).injective (F.frame.symm.injective he)))

theorem action_frame (u : U) (i : I) (b : ZMod 2) :
    (u : Equiv.Perm X) (F.frame (i,b))=F.frame (F.top u i,b+F.offset u i) :=
  F.frame.symm.injective ((F.action_coordinates u i b).trans
    (F.frame.symm_apply_apply _).symm)

/-- The original U action on its actual kernel is the actual top action
on the correlated bit coordinates, with the inverse on the coordinate. -/
theorem bits_conjNormal (u : U) (k : F.top.ker) (i : I) :
    F.bits (MulAut.conjNormal u k) i=F.bits k ((F.top u)⁻¹ i) := by
  let j := (F.top u)⁻¹ i
  have hj : F.top u j=i := Equiv.apply_symm_apply (F.top u) i
  have he : (((MulAut.conjNormal u k : F.top.ker):U):Equiv.Perm X)
      ((u:Equiv.Perm X) (F.frame (j,0)))=
        (u:Equiv.Perm X) (((k:U):Equiv.Perm X) (F.frame (j,0))) := by
    change ((u:Equiv.Perm X)*((k:U):Equiv.Perm X)*(u:Equiv.Perm X)⁻¹)
      ((u:Equiv.Perm X) (F.frame (j,0)))=_
    simp only [Equiv.Perm.mul_apply,Equiv.Perm.inv_def,Equiv.symm_apply_apply]
  rw [F.action_frame,F.kernel_action_frame,F.kernel_action_frame,F.action_frame] at he
  have hbits := congrArg Prod.snd (F.frame.injective he)
  simp only [hj,zero_add] at hbits
  exact add_left_cancel (hbits.trans (add_comm _ _))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
