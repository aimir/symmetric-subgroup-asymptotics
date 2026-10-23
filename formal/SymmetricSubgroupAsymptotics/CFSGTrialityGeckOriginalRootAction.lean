import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalRootFamily
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyFaithfulness

/-! Faithful action of ORIGINAL triality automorphisms on the intrinsic
conjugate highest-root family. This is the actual previously counted
family; no identification with a polar space or hexagon is presumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalRootAction
open CFSGTrialityGeckOriginalIndexSquare CFSGTrialityGeckOriginalRootFamily
variable (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)]

def rootLabel : originalLongFamily q→Subgroup (CFSG.Models.TrialityD4 q) := Subtype.val

theorem rootLabel_injective : Function.Injective (rootLabel q) := Subtype.val_injective

theorem rootLabel_stable (f : MulAut (CFSG.Models.TrialityD4 q)) (x : originalLongFamily q) :
    ∃y : originalLongFamily q,rootLabel q y=(rootLabel q x).map f.toMonoidHom := by
  obtain ⟨g,hg⟩ := x.property
  obtain ⟨h,hh⟩ := automorphism_maps_original_conjugate_line q f g
  refine ⟨⟨(originalLongLine q).map (MulAut.conj h).toMonoidHom,⟨h,rfl⟩⟩,?_⟩
  change (originalLongLine q).map (MulAut.conj h).toMonoidHom=x.val.map f.toMonoidHom
  rw [←hg]
  exact hh.symm

def rootActionHom : MulAut (CFSG.Models.TrialityD4 q) →* Equiv.Perm (originalLongFamily q) :=
  CFSGSubgroupFamilyPermutation.permutationHom (rootLabel q) (rootLabel_injective q)
    (rootLabel_stable q)

theorem rootLabel_action (f : MulAut (CFSG.Models.TrialityD4 q)) (x : originalLongFamily q) :
    rootLabel q (rootActionHom q f x)=(rootLabel q x).map f.toMonoidHom :=
  CFSGSubgroupFamilyPermutation.label_permutation (rootLabel q) (rootLabel_injective q)
    (rootLabel_stable q) f x

theorem rootActionHom_injective : Function.Injective (rootActionHom q) := by
  let x0 : originalLongFamily q := ⟨originalLongLine q,⟨1,by
    simp only [map_one]
    change (originalLongLine q).map (MonoidHom.id (CFSG.Models.TrialityD4 q))=originalLongLine q
    exact Subgroup.map_id _⟩⟩
  exact CFSGSubgroupFamilyFaithfulness.permutationHom_injective (rootLabel q)
    (rootLabel_injective q) (rootLabel_stable q) x0
    (originalLongLine_ne_bot q) (originalLongLine_ne_top q)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalRootAction
