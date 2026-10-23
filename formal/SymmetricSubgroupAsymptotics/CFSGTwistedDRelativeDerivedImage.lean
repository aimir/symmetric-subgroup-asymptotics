import SymmetricSubgroupAsymptotics.CFSGTwistedDPreimageCommutator
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedProjectiveImage
import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv

/-! The actual original Derived action range equals the action range of
the independently defined literal relative-root subgroup. The original
model transport retains its source simplicity assumption only. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeDerivedImage
open CFSGOrthogonalDSerreMatrices CFSGTwistedDRelativeElementaryGroup
open CFSGTwistedDFixedA2 CFSGTwistedDFixedCentralCocycle CFSGTwistedDDerivedPairedRoots
open CFSGTwistedDPreimageRelativeStructure CFSGTwistedDPreimageCommutator

def relativeImageAction (s : ℕ) (q : CFSG.PrimePower) :=
  (elementaryImageAction (q.Extension 2) (s + 4) (by omega)).comp
    (Subgroup.inclusion (relativeRootGroup_le_elementary (s + 2) q))

theorem relative_image_le_derived_image (s : ℕ) (q : CFSG.PrimePower) :
    (relativeImageAction s q).range ≤ (CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range := by
  rintro y ⟨r, rfl⟩
  obtain ⟨u, hu, he⟩ :=
    CFSGTwistedDRetainedRelativeGroup.relativeRootGroup_le_derived_unit_image s q r.property
  have hr : u = Subgroup.inclusion (relativeRootGroup_le_elementary (s + 2) q) r :=
    Subtype.ext he
  rw [hr] at hu
  exact hu

theorem derived_image_le_relative_image (s : ℕ) (q : CFSG.PrimePower) :
    (CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range ≤ (relativeImageAction s q).range := by
  let μ := preimageToImage s q
  let η := (CFSGTwistedDFixedCentralCocycle.fixedImageAction s q).rangeRestrict
  have hμ : (commutator (PreimageGroup s q)).map μ =
      commutator (CFSGTwistedDFixedCentralCocycle.fixedImageAction s q).range := by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective μ (preimageToImage_surjective s q)]
  have hη : (commutator (Fixed s q)).map η =
      commutator (CFSGTwistedDFixedCentralCocycle.fixedImageAction s q).range := by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective η (CFSGTwistedDFixedCentralCocycle.fixedImageAction s q).rangeRestrict_surjective]
  rintro y ⟨d, rfl⟩
  have hd : η d.val ∈ commutator (CFSGTwistedDFixedCentralCocycle.fixedImageAction s q).range := by
    rw [← hη]
    exact ⟨d.val, d.property, rfl⟩
  rw [← hμ] at hd
  obtain ⟨u, hu, he⟩ := hd
  let r : relativeRootGroup (s + 2) q :=
    ⟨naturalInclusion s q u, commutator_le_relative s q hu⟩
  refine ⟨r, ?_⟩
  exact congrArg Subtype.val he

theorem action_ranges_eq (s : ℕ) (q : CFSG.PrimePower) :
    (CFSGTwistedDDerivedPairedRoots.derivedImageAction s q).range = (relativeImageAction s q).range :=
  le_antisymm (derived_image_le_relative_image s q) (relative_image_le_derived_image s q)

def originalProjectiveRelativeImageEquiv (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    CFSG.Models.TwistedD (s + 4) q ≃*
      ((relativeImageAction s q).range ⧸ Subgroup.center (relativeImageAction s q).range) :=
  (CFSGTwistedDDerivedProjectiveImage.originalProjectiveImageEquiv s q).trans
    (CFSGCenterQuotientEquiv.equiv (MulEquiv.subgroupCongr (action_ranges_eq s q)))

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeDerivedImage
