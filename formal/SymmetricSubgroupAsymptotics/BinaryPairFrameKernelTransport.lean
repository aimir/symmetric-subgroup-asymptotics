import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-!
# Transport of literal pair-kernel bits

Physical-point relabelling and pair-index relabelling do not change the
retained flip carried by an element of a binary pair kernel.  This file
packages the corresponding kernel elements and records the two literal
bit identities.  The statements are intentionally about the actual frame,
rather than an abstractly isomorphic binary module.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

variable {X Y I J : Type*} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U I)

/-- Transport a literal pair-kernel element through a relabelling of the
physical point set. -/
def relabelKernel (e : X ≃ Y) (k : F.top.ker) :
    (F.relabelPoints e).top.ker :=
  ⟨sourceRelabelEquiv (U := U) e k.1, by
    apply Equiv.ext
    intro i
    rw [F.relabelPoints_top_sourceRelabelEquiv, k.2]⟩

/-- Physical-point relabelling preserves every retained flip bit. -/
@[simp] theorem relabelKernel_bits (e : X ≃ Y) (k : F.top.ker) (i : I) :
    (F.relabelPoints e).bits (F.relabelKernel e k) i = F.bits k i := by
  have hnew := (F.relabelPoints e).kernel_action_frame
    (F.relabelKernel e k) i 0
  have hold := congrArg e (F.kernel_action_frame k i 0)
  have hperm :
      ((((F.relabelKernel e k).1 : relabelSubgroup e U) :
          Equiv.Perm Y)) =
        e.permCongr (((k.1 : U) : Equiv.Perm X)) := by
    change
      (((sourceRelabelEquiv (U := U) e k.1 : relabelSubgroup e U) :
          Equiv.Perm Y)) = _
    exact MulEquiv.coe_subgroupMap_apply e.permCongrHom U k.1
  have hpoints :
      (F.relabelPoints e).frame
          (i, (F.relabelPoints e).bits (F.relabelKernel e k) i) =
        (F.relabelPoints e).frame (i, F.bits k i) := by
    calc
      _ = (((F.relabelKernel e k : (F.relabelPoints e).top.ker) :
            relabelSubgroup e U) : Equiv.Perm Y)
          ((F.relabelPoints e).frame (i, 0)) := by
            simpa only [zero_add] using hnew.symm
      _ = _ := by
        rw [hperm, Equiv.permCongr_apply, F.relabelPoints_frame,
          Equiv.symm_apply_apply, F.relabelPoints_frame]
        simpa only [zero_add] using hold
  have hpairs :
      (i, (F.relabelPoints e).bits (F.relabelKernel e k) i) =
        (i, F.bits k i) :=
    (F.relabelPoints e).frame.injective hpoints
  have hbits := congrArg (fun p : I × ZMod 2 => p.2) hpairs
  exact hbits

/-- Transport a literal pair-kernel element through a relabelling of only
the pair indices. -/
def reindexKernel (e : I ≃ J) (k : F.top.ker) :
    (F.reindex e).top.ker :=
  ⟨k.1, by
    apply Equiv.ext
    intro j
    change e (F.top k.1 (e.symm j)) = j
    rw [k.2]
    exact e.apply_symm_apply j⟩

/-- Pair-index relabelling evaluates the old bit at the corresponding old
pair coordinate. -/
@[simp] theorem reindexKernel_bits (e : I ≃ J) (k : F.top.ker) (j : J) :
    (F.reindex e).bits (F.reindexKernel e k) j = F.bits k (e.symm j) := by
  have hnew := (F.reindex e).kernel_action_frame (F.reindexKernel e k) j 0
  have hold := F.kernel_action_frame k (e.symm j) 0
  have hpoints :
      (F.reindex e).frame
          (j, (F.reindex e).bits (F.reindexKernel e k) j) =
        (F.reindex e).frame (j, F.bits k (e.symm j)) := by
    calc
      _ = ((k.1 : U) : Equiv.Perm X) ((F.reindex e).frame (j, 0)) := by
        simpa only [zero_add, reindexKernel] using hnew.symm
      _ = _ := by
        simpa only [F.reindex_frame, zero_add] using hold
  have hpairs :
      (j, (F.reindex e).bits (F.reindexKernel e k) j) =
        (j, F.bits k (e.symm j)) :=
    (F.reindex e).frame.injective hpoints
  have hbits := congrArg (fun p : J × ZMod 2 => p.2) hpairs
  exact hbits

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
