import SymmetricSubgroupAsymptotics.BinaryPairSharedBinding
import SymmetricSubgroupAsymptotics.SchreierKernelGenerators

/-! A quotient-sized Schreier certificate identifies the entire literal
flip kernel. No original-group enumeration or declared order is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X H ι : Type} [Group H] {w d : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem mem_coordinateSubgroup_of_action
    (C : Submodule (ZMod 2) (Fin w → ZMod 2)) (u : U) (v : Fin w → ZMod 2)
    (hv : v∈C)
    (h : ∀ p : Fin w × ZMod 2,
      F.frame.symm ((u : Equiv.Perm X) (F.frame p))=(p.1,p.2+v p.1)) :
    u∈F.coordinateSubgroup C := by
  have hu : F.top u=1 := by
    apply Equiv.ext
    intro i
    have he := congrArg Prod.fst (h (i,0))
    rw [F.intertwine] at he
    exact he
  let k : F.top.ker := ⟨u,hu⟩
  apply (F.kernel_mem_coordinateSubgroup C k).mpr
  have hb : F.bits k=v := by
    funext i
    simpa only [zero_add] using congrArg Prod.snd (h (i,0))
  rwa [hb]

/-- All actual Schreier generators lie in the proposed flip chart, and
each chart basis vector is witnessed by an original permutation. These
two containments identify the full correlated kernel. -/
theorem kernelSpace_eq_of_schreier (C : BinaryCoordinateSpace w d)
    (generators : ι → U) (hgen : Subgroup.closure (Set.range generators)=⊤)
    (χ : U →* H) (hχ : χ.ker=F.top.ker)
    (sectionMap : H → U) (hsection : ∀ q, χ (sectionMap q)=q)
    (hidentity : sectionMap 1=1)
    (hwords : ∀ q j, schreierWords generators χ sectionMap (q,j)∈F.coordinateSubgroup C.space)
    (hbasis : ∀ i, C.inclusion (Pi.single i 1)∈F.kernelSpace) :
    F.kernelSpace=C.space := by
  have hk : F.top.ker≤F.coordinateSubgroup C.space := by
    rw [← hχ,schreier_kernel_generated generators hgen χ sectionMap hsection hidentity]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨⟨q,j⟩,rfl⟩
    exact hwords q j
  apply le_antisymm
  · intro v hv
    obtain ⟨k,rfl⟩ := hv
    exact (F.kernel_mem_coordinateSubgroup C.space k.toMul).mp (hk k.toMul.property)
  · exact C.le_of_basis_mem F.kernelSpace hbasis

end SymmetricSubgroupAsymptotics.BinaryPairFrame
