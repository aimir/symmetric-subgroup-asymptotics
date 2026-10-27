import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveBaseActions

/-! Original B source parent relations, with their natural coefficient
rows proved by applying the actual representation. A matrix equality is
never used in the reverse direction to infer a source relation. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveInductionParents
open CFSG.Models.Chevalley CFSGOrthogonalBSerreMatrices
open CFSGOrthogonalBOriginalRootCandidates CFSGOrthogonalBOriginalPositiveSourceProfile
open CFSGOrthogonalBUniformPositiveTables CFSGOrthogonalBOriginalPositivePrimitiveFamily
variable (r : ℕ)

private theorem parent_row (i : Fin r) (p j : PositiveIndex r) (c : ℚ)
    (hp : ⁅rootVector (CartanMatrix.B r).transpose false i,
      CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r p⁆ =
        c • CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j) :
    raising r i p = c • Pi.single j 1 := by
  have h := congrArg (fun x => positiveCoordinates r (rationalOrthogonalRepresentation r x)) hp
  have hE : rationalOrthogonalRepresentation r (rootVector (CartanMatrix.B r).transpose false i) =
      positive ℚ r i := rationalOrthogonalRepresentation_E r i
  simpa only [LieHom.map_lie, map_smul, hE, source_image,
    positive_coordinates_matrix, raising] using h

theorem induction_parent (j : PositiveIndex r) (hj : 1 < height r j) :
    ∃ (i : Fin r) (p : PositiveIndex r) (c : ℚ), c ≠ 0 ∧ 0 < height r p ∧
      height r p + 1 = height r j ∧
      ⁅rootVector (CartanMatrix.B r).transpose false i,
        CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r p⁆ =
          c • CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r j ∧
      raising r i p = c • Pi.single j 1 := by
  cases j with
  | inl j => simp [height] at hj
  | inr j =>
    obtain ⟨i, p, c, hc, hp, hh, he⟩ :=
      CFSGOrthogonalBOriginalPositiveSourceProfile.induction_parent r j hj
    have he' : ⁅rootVector (CartanMatrix.B r).transpose false i,
        CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r (.inr p)⁆ =
          c • CFSGOrthogonalBOriginalPositivePrimitiveFamily.source r (.inr j) := he
    exact ⟨i, .inr p, c, hc, hp, hh, he', parent_row r i (.inr p) (.inr j) c he'⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalPositiveInductionParents
