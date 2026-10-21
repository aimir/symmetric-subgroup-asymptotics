import SymmetricSubgroupAsymptotics.BinaryHeisenbergFullSplitModel
import SymmetricSubgroupAsymptotics.BinaryPairSplitAffineRows
import SymmetricSubgroupAsymptotics.BinaryPairSplitRecognition
import SymmetricSubgroupAsymptotics.BinaryPairInvariantAxes

/-! Full natural pair kernels make the displayed Heisenberg semidirect
model literally equivalent to the original action. The normal axis is
then recovered from the same original subgroup, rather than enumerated. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryHeisenbergEightNaturalHeads
open BinaryHeisenbergFullSplitModel
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 8))

private def heisenbergFullPermutationHom : Model →* Equiv.Perm X where
  toFun g := F.affinePermutation g.right.val g.left.toAdd
  map_one' := by
    apply Equiv.ext
    intro x
    obtain ⟨⟨i,b⟩,rfl⟩ := F.frame.surjective x
    rw [F.affinePermutation_apply_frame]
    simp
  map_mul' g h := by
    rw [F.affinePermutation_mul_formula]
    congr 1 <;> rfl

private theorem heisenbergFullPermutationHom_injective :
    Function.Injective F.heisenbergFullPermutationHom := by
  intro g h he
  have hh := F.affinePermutation_coordinates_injective he
  apply SemidirectProduct.ext
  · exact Multiplicative.toAdd.injective hh.2
  · exact Subtype.ext hh.1

private theorem heisenbergFullPermutationHom_mem
    (hH : F.top.range = H) (hK : F.kernelSpace = ⊤) (g : Model) :
    F.heisenbergFullPermutationHom g ∈ U := by
  have hzero := F.eq_splitAffineAction_of_translation_mem (fun _ => hK.symm ▸ Submodule.mem_top)
  apply (show F.splitAffineAction ≤ U from le_of_eq hzero.symm)
  exact Subgroup.subset_closure
    ⟨⟨g.right.val, hH.symm ▸ g.right.property⟩, g.left.toAdd,
      hK.symm ▸ Submodule.mem_top, rfl⟩

/-- Every model element retains its original physical permutation. -/
def heisenbergFullSplitEquiv (hH : F.top.range = H) (hK : F.kernelSpace = ⊤) :
    Model ≃* U :=
  MulEquiv.ofBijective
    (F.heisenbergFullPermutationHom.codRestrict U (F.heisenbergFullPermutationHom_mem hH hK))
    ⟨fun _ _ he => F.heisenbergFullPermutationHom_injective (congrArg Subtype.val he), by
      intro u
      let t : H := ⟨F.top u, hH ▸ (F.top.rangeRestrict u).property⟩
      refine ⟨⟨Multiplicative.ofAdd (F.affineTranslation u),t⟩, ?_⟩
      apply Subtype.ext
      exact F.affinePermutation_original u⟩

/-- The literal model translation axis is the original normal intersection. -/
theorem heisenbergFullSplitEquiv_inl_mem_iff
    (hH : F.top.range = H) (hK : F.kernelSpace = ⊤)
    (N : Subgroup U) (v : V) :
    F.heisenbergFullSplitEquiv hH hK (SemidirectProduct.inl (Multiplicative.ofAdd v)) ∈ N ↔
      v ∈ F.ambientAxis N := by
  let u := F.heisenbergFullSplitEquiv hH hK
    (SemidirectProduct.inl (Multiplicative.ofAdd v))
  have hku : F.top u = 1 := by
    apply Equiv.ext
    intro i
    have hx := F.affine_action_frame u i 0
    change F.physicalFlip v (F.frame (i,0)) = _ at hx
    rw [F.physicalFlip_apply_frame] at hx
    exact (congrArg Prod.fst (F.frame.injective hx)).symm
  let k : F.top.ker := ⟨u,hku⟩
  have hbits : F.bits k = v := by
    funext i
    have hx := F.affine_action_frame u i 0
    change F.physicalFlip v (F.frame (i,0)) = _ at hx
    have ht : F.affineTranslation u = F.bits k := F.affineTranslation_kernel k
    rw [F.physicalFlip_apply_frame,hku,ht] at hx
    simpa only [zero_add,Equiv.Perm.one_apply] using
      (congrArg Prod.snd (F.frame.injective hx)).symm
  have h := F.bits_mem_ambientAxis N k
  rw [hbits] at h
  exact h.symm

end SymmetricSubgroupAsymptotics.BinaryPairFrame
