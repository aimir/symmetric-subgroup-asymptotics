import SymmetricSubgroupAsymptotics.BinaryDegree16CanonicalSplitModels
import SymmetricSubgroupAsymptotics.BinarySelectedCatalogueModel16T1332
import SymmetricSubgroupAsymptotics.BinarySelectedPairDirectOwners16
import SymmetricSubgroupAsymptotics.BinaryExceptional16PhysicalProfile
import SymmetricSubgroupAsymptotics.BinaryLiteral16T1332PhysicalProfile
import SymmetricSubgroupAsymptotics.BinaryCarrierMasterEnvelopeCoverage16

/-!
# Literal owners for every degree-sixteen split residual

The structural split residual is transported, with its original normal
axis, to one of the three literal catalogue actions.  The 16T1098 branch
has a direct even-prefix entry on every transported normal.  The 16T1086
branch has either the same direct entry or its exact reversible carrier,
which is full on one original C4 block and three critical D8 blocks through
every exterior continuation.  The 16T1332
branch enters the proved master-envelope menu.  Thus no coordinate model
or untransported numerical row remains between the structural frontier and
the finite analytic owners.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegree16SplitCatalogueOwners

open SymmetricSubgroupAsymptotics
open BinaryDegree16SplitFrontier
open BinaryDegree16CanonicalSplitModels
open FullSubdirectGoursat JointCapacityRow BinaryCarrierMasterMenu
open BinaryCarrierMasterEnvelopes

private theorem relabelSubgroup_eq_conj_smul {X : Type*}
    (g : Equiv.Perm X) (T : Subgroup (Equiv.Perm X)) :
    relabelSubgroup g T=MulAut.conj g • T := by
  rfl

private theorem residual_relabel_eq_canonical
    {U : Subgroup (Equiv.Perm (Fin 16))}
    {N : Subgroup U} [N.Normal]
    (R : SplitResidual U N)
    {V : Subgroup (Equiv.Perm (Fin 8))}
    {S : Submodule (ZMod 2) (Fin 8 → ZMod 2)}
    (C : CanonicalModel R.frame.top.range R.frame.kernelSpace V S) :
    relabelSubgroup
        ((R.frame.physicalFlip R.conjugator).trans
          (R.frame.frame.symm.trans (binaryCoordinateRelabel C.relabel))) U=
      binaryCoordinateSplitAction V S := by
  have hconj : MulAut.conj (R.frame.physicalFlip R.conjugator) • U=
      R.frame.splitAffineAction := by
    change U.map
      (MulAut.conj (R.frame.physicalFlip R.conjugator)).toMonoidHom=
        R.frame.splitAffineAction
    exact R.conjugate_eq
  rw [← relabelSubgroup_trans,relabelSubgroup_eq_conj_smul,hconj,
    ← relabelSubgroup_trans,
    R.frame.relabelSubgroup_frame_symm_splitAffineAction]
  exact C.coordinate_action_eq

private theorem compare_relabels {X Y : Type*}
    {U : Subgroup (Equiv.Perm X)} {V : Subgroup (Equiv.Perm X)}
    (e d : X ≃ Y) {W : Subgroup (Equiv.Perm Y)}
    (he : relabelSubgroup e U=W) (hd : relabelSubgroup d V=W) :
    relabelSubgroup (e.trans d.symm) U=V := by
  rw [← relabelSubgroup_trans,he,← hd,relabelSubgroup_symm]

/-- The exact finite owner attached to a split residual.  Every constructor
retains one ambient point conjugation and transports the original normal by
that same conjugation. -/
inductive CatalogueOwner
    (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Prop
  | t1098 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinaryPairBinding16T1098.Original)
      (entry : Nonempty (AcceptedEntry BinaryPairBinding16T1098.Original
        (actionConjugacyNormal g hg N)))
  | t1086 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinaryPairBinding16T1086.Original)
      (owner : Nonempty (AcceptedEntry BinaryPairBinding16T1086.Original
          (actionConjugacyNormal g hg N)) ∨
        Nonempty (BinaryExceptional16CyclicOwner.AxisOwner
          (actionConjugacyNormal g hg N)))
  | t1332 (g : Equiv.Perm (Fin 16))
      (hg : MulAut.conj g • U=BinarySelectedCatalogue16T1332.Original)
      (row : ∃ label : Label,
        (BinaryCarrierWord.actualRow
          (A := BinaryCarrierMasterEnvelopeCoverage16T1332.factor)
          ⟨actionConjugacyNormal g hg N,
            actionConjugacyNormal_normal g hg N⟩).EffectivelyBoundedBy
            (envelope label))
      (profile : BinaryCarrierParameterProfiles.PhysicalFamily 0 0 2 (Fin 16))
      (profile_eq : profile.1=U)

/-- Every retained split residual enters a literal finite owner.  This is
the complete finite bridge: the 8T9 coordinate model is 16T1098, the 8T10
model is 16T1086, and the 8T18 model is 16T1332. -/
theorem residual_catalogue_owner
    {U : Subgroup (Equiv.Perm (Fin 16))}
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    {N : Subgroup U} [N.Normal]
    (R : SplitResidual U N) : CatalogueOwner U N := by
  rcases residual_canonically_covered hU R with h9 | h10 | h18
  · obtain ⟨C⟩ := h9
    let e := (R.frame.physicalFlip R.conjugator).trans
        (R.frame.frame.symm.trans (binaryCoordinateRelabel C.relabel))
    let d := BinaryPairBinding16T1098.physicalFrame.frame.symm.trans
      (binaryCoordinateRelabel BinarySelectedCatalogue16T1098.labelRelabel)
    let g : Equiv.Perm (Fin 16) := e.trans d.symm
    have he : relabelSubgroup e U=
        binaryCoordinateSplitAction BinarySelectedAxis8T9.Action
          BinarySelectedAxis8T9.selectedAugmentation :=
      residual_relabel_eq_canonical R C
    have hd : relabelSubgroup d BinaryPairBinding16T1098.Original=
        binaryCoordinateSplitAction BinarySelectedAxis8T9.Action
          BinarySelectedAxis8T9.selectedAugmentation :=
      BinarySelectedCatalogue16T1098.physical_original_eq_canonical
    have hg' : relabelSubgroup g U=BinaryPairBinding16T1098.Original :=
      compare_relabels e d he hd
    have hg : MulAut.conj g • U=BinaryPairBinding16T1098.Original := by
      simpa only [relabelSubgroup_eq_conj_smul] using hg'
    have htarget : IsPGroup 2 BinaryPairBinding16T1098.Original :=
      hU.of_equiv (actionConjugacyEquiv g hg)
    exact .t1098 g hg
      (BinarySelectedPairDirectOwners16.T1098.accepted_entry htarget
        (actionConjugacyNormal g hg N))
  · obtain ⟨C⟩ := h10
    let e := (R.frame.physicalFlip R.conjugator).trans
        (R.frame.frame.symm.trans (binaryCoordinateRelabel C.relabel))
    let d := BinaryPairBinding16T1086.physicalFrame.frame.symm.trans
      (binaryCoordinateRelabel BinarySelectedCatalogue16T1086.labelRelabel)
    let g : Equiv.Perm (Fin 16) := e.trans d.symm
    have he : relabelSubgroup e U=
        binaryCoordinateSplitAction BinarySelectedAxis8T10.Action
          BinarySelectedAxis8T10.selectedAugmentation :=
      residual_relabel_eq_canonical R C
    have hd : relabelSubgroup d BinaryPairBinding16T1086.Original=
        binaryCoordinateSplitAction BinarySelectedAxis8T10.Action
          BinarySelectedAxis8T10.selectedAugmentation :=
      BinarySelectedCatalogue16T1086.physical_original_eq_canonical
    have hg' : relabelSubgroup g U=BinaryPairBinding16T1086.Original :=
      compare_relabels e d he hd
    have hg : MulAut.conj g • U=BinaryPairBinding16T1086.Original := by
      simpa only [relabelSubgroup_eq_conj_smul] using hg'
    have htarget : IsPGroup 2 BinaryPairBinding16T1086.Original :=
      hU.of_equiv (actionConjugacyEquiv g hg)
    rcases BinarySelectedPairDirectOwners16.T1086.accepted_entry_or_transport htarget
        (actionConjugacyNormal g hg N) with hentry | ⟨hsource,haxis⟩
    · exact .t1086 g hg (Or.inl hentry)
    · exact .t1086 g hg (Or.inr ⟨
        BinaryExceptional16CyclicOwner.AxisOwner.ofEqualities hsource haxis⟩)
  · obtain ⟨C⟩ := h18
    let e := (R.frame.physicalFlip R.conjugator).trans
        (R.frame.frame.symm.trans (binaryCoordinateRelabel C.relabel))
    let d := BinarySelectedCatalogue16T1332.physicalFrame.frame.symm.trans
      (binaryCoordinateRelabel BinarySelectedCatalogue16T1332.labelRelabel)
    let g : Equiv.Perm (Fin 16) := e.trans d.symm
    have he : relabelSubgroup e U=
        binaryCoordinateSplitAction BinarySelectedAxis8T18.Action
          BinarySelectedAxis8T18.selectedAugmentation :=
      residual_relabel_eq_canonical R C
    have hd : relabelSubgroup d BinarySelectedCatalogue16T1332.Original=
        binaryCoordinateSplitAction BinarySelectedAxis8T18.Action
          BinarySelectedAxis8T18.selectedAugmentation :=
      BinarySelectedCatalogue16T1332.physical_original_eq_canonical
    have hg' : relabelSubgroup g U=BinarySelectedCatalogue16T1332.Original :=
      compare_relabels e d he hd
    have hg : MulAut.conj g • U=BinarySelectedCatalogue16T1332.Original := by
      simpa only [relabelSubgroup_eq_conj_smul] using hg'
    exact .t1332 g hg
      (BinaryCarrierMasterEnvelopeCoverage16T1332.actualRow_effectivelyBoundedBy_envelope
        ⟨actionConjugacyNormal g hg N,
          actionConjugacyNormal_normal g hg N⟩)
      (BinaryLiteral16T1332PhysicalProfile.transportedPhysicalFamily g hg)
      rfl

/-- The complete degree-sixteen owner interface: the intrinsic reduction
either already supplies a direct fusion entry, or the exact split residual
enters one of the three literal finite owners above. -/
def CompleteOwner
    (U : Subgroup (Equiv.Perm (Fin 16)))
    (N : Subgroup U) [N.Normal] : Prop :=
  AcceptedAxis U N ∨ CatalogueOwner U N

theorem complete_axis_owner
    (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    (N : Subgroup U) [N.Normal] : CompleteOwner U N := by
  rcases axis_frontier U hU N with h | h
  · exact Or.inl h
  · obtain ⟨R⟩ := h
    exact Or.inr (residual_catalogue_owner hU R)

end SymmetricSubgroupAsymptotics.BinaryDegree16SplitCatalogueOwners
