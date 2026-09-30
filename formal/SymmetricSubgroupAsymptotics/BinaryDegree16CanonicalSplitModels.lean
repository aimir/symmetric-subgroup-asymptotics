import SymmetricSubgroupAsymptotics.BinaryDegree16SplitTopClassification
import SymmetricSubgroupAsymptotics.BinarySelectedAxisAugmentation
import SymmetricSubgroupAsymptotics.BinaryTwoOrbitAugmentationEquivariantTransport

/-!
# Canonical coordinate models for the degree-sixteen split residual

The exact top-axis classification and the original-module theorem use the
same ambient relabelling.  Equivariant orbit transport therefore identifies
the entire correlated flip module, and hence the entire split affine action,
with one of three literal coordinate models.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryDegree16CanonicalSplitModels

open SymmetricSubgroupAsymptotics
open BinaryDegree16SplitFrontier
open BinaryDegreeEightElementaryTopClassification
open PermutationBinaryTwoOrbitSplit

theorem relabelSubgroup_eq_conj_smul (g : Equiv.Perm (Fin 8))
    (T : Subgroup (Equiv.Perm (Fin 8))) :
    relabelSubgroup g T=MulAut.conj g • T := by
  rfl

/-- A compact record retaining the one label permutation which transports
both the full top and its correlated flip module. -/
structure CanonicalModel (T : Subgroup (Equiv.Perm (Fin 8)))
    (M : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (targetTop : Subgroup (Equiv.Perm (Fin 8)))
    (targetModule : Submodule (ZMod 2) (Fin 8 → ZMod 2)) where
  relabel : Equiv.Perm (Fin 8)
  top_eq : relabelSubgroup relabel T=targetTop
  module_eq : binaryRelabelModule relabel M=targetModule

def CanonicallyCovered (T : Subgroup (Equiv.Perm (Fin 8)))
    (M : Submodule (ZMod 2) (Fin 8 → ZMod 2)) : Prop :=
  Nonempty (CanonicalModel T M (elementaryTops 0)
    BinarySelectedAxis8T9.selectedAugmentation) ∨
  Nonempty (CanonicalModel T M (elementaryTops 1)
    BinarySelectedAxis8T10.selectedAugmentation) ∨
  Nonempty (CanonicalModel T M (elementaryTops 2)
    BinarySelectedAxis8T18.selectedAugmentation)

private theorem relabel_augmentation_eq
    {T V : Subgroup (Equiv.Perm (Fin 8))}
    (g : Equiv.Perm (Fin 8)) (hg : MulAut.conj g • T=V)
    (H : Subgroup T) (selected : Subgroup V)
    (haxis : actionConjugacyNormal g hg H=selected)
    (M S : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (o₁ o₂ : MulAction.orbitRel.Quotient H (Fin 8))
    (hne : o₁≠o₂)
    (hM : M=twoOrbitAugmentation H o₁ o₂)
    (hcanonical : ∀ p q : MulAction.orbitRel.Quotient selected (Fin 8),
      p≠q → twoOrbitAugmentation selected p q=S) :
    binaryRelabelModule g M=S := by
  let eT : T ≃* V := actionConjugacyEquiv g hg
  let eH : H ≃* selected :=
    (H.equivMapOfInjective eT.toMonoidHom eT.injective).trans
      (MulEquiv.subgroupCongr haxis)
  have he : ∀ h : H,∀ x : Fin 8,g (h • x)=eH h • g x := by
    intro h x
    have hcoe : ((eH h : selected) : Equiv.Perm (Fin 8))=
        g*((h : T) : Equiv.Perm (Fin 8))*g⁻¹ := by
      exact actionConjugacyEquiv_coe g hg (h : T)
    change g (((h : T) : Equiv.Perm (Fin 8)) x)=
      ((eH h : selected) : Equiv.Perm (Fin 8)) (g x)
    rw [hcoe]
    simp
  let p := equivariantOrbitEquiv H selected eH g he o₁
  let q := equivariantOrbitEquiv H selected eH g he o₂
  have hpq : p≠q := fun hp => hne
    ((equivariantOrbitEquiv H selected eH g he).injective hp)
  calc
    binaryRelabelModule g M =
        binaryRelabelModule g (twoOrbitAugmentation H o₁ o₂) :=
      congrArg (binaryRelabelModule g) hM
    _ = twoOrbitAugmentation selected p q :=
      binaryRelabelModule_twoOrbitAugmentation_equivariant
        H selected eH g he o₁ o₂
    _ = S := hcanonical p q hpq

/-- The full coordinate split construction follows the same simultaneous
top-and-module relabelling stored in a canonical model. -/
theorem CanonicalModel.coordinate_action_eq
    {T V : Subgroup (Equiv.Perm (Fin 8))}
    {M S : Submodule (ZMod 2) (Fin 8 → ZMod 2)}
    (C : CanonicalModel T M V S) :
    relabelSubgroup (binaryCoordinateRelabel C.relabel)
        (binaryCoordinateSplitAction T M)=
      binaryCoordinateSplitAction V S := by
  rw [relabelSubgroup_binaryCoordinateSplitAction,C.top_eq,C.module_eq]

/-- Every retained split residual has one of the three literal canonical
top-and-module coordinate models.  This is stronger than a top-only finite
classification: the complete correlated kernel is transported too. -/
theorem residual_canonically_covered
    {U : Subgroup (Equiv.Perm (Fin 16))}
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    {N : Subgroup U} [N.Normal]
    (R : SplitResidual U N) :
    CanonicallyCovered R.frame.top.range R.frame.kernelSpace := by
  letI : MulAction.IsPretransitive R.frame.top.range (Fin 8) :=
    R.frame.top_pretransitive
  let H := (R.frame.sectionTopRepresentation N).ker
  obtain ⟨hd,_,_,⟨data⟩,_,_,_⟩ := R.residual
  obtain ⟨o₁,o₂,hne,_,hM,_⟩ :=
    permutationBinary_twoBlockCharacter_original_module_eq
      (R.frame.top_isPGroup hU) (0 : Fin 8) (Nat.card_fin 8)
      (R.frame.sectionTopRepresentation N)
      R.frame.kernelTopPermutationSubrepresentation
      (R.frame.sectionTopIntertwiner N)
      (R.frame.normalSpace N).mkQ_surjective hd data
  change R.frame.kernelSpace=twoOrbitAugmentation H o₁ o₂ at hM
  rcases BinaryDegree16SplitTopClassification.residual_exact_axis hU R with
      ⟨g,hg,haxis⟩ | ⟨g,hg,haxis⟩ | ⟨g,hg,haxis⟩
  · left
    refine ⟨⟨g,?_,?_⟩⟩
    · exact (relabelSubgroup_eq_conj_smul g R.frame.top.range).trans hg
    · exact relabel_augmentation_eq g hg H elementaryAxis8T9 haxis
        R.frame.kernelSpace BinarySelectedAxis8T9.selectedAugmentation
        o₁ o₂ hne hM BinarySelectedAxis8T9.augmentation_eq_selected
  · right; left
    refine ⟨⟨g,?_,?_⟩⟩
    · exact (relabelSubgroup_eq_conj_smul g R.frame.top.range).trans hg
    · exact relabel_augmentation_eq g hg H elementaryAxis8T10 haxis
        R.frame.kernelSpace BinarySelectedAxis8T10.selectedAugmentation
        o₁ o₂ hne hM BinarySelectedAxis8T10.augmentation_eq_selected
  · right; right
    refine ⟨⟨g,?_,?_⟩⟩
    · exact (relabelSubgroup_eq_conj_smul g R.frame.top.range).trans hg
    · exact relabel_augmentation_eq g hg H elementaryAxis8T18 haxis
        R.frame.kernelSpace BinarySelectedAxis8T18.selectedAugmentation
        o₁ o₂ hne hM BinarySelectedAxis8T18.augmentation_eq_selected

end SymmetricSubgroupAsymptotics.BinaryDegree16CanonicalSplitModels
