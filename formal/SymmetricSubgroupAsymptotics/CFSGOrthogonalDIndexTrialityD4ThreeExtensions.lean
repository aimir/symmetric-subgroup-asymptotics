import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4CrossExtensions
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2ProjectiveLines

/-! Actual Q-singular three-spaces above the fixed D4 root plane are
exactly the pairs of opposite maximal-extension parameters. This is
derived from original restriction and residual rank-one factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

abbrev ResidualSingularLines := {L : Submodule K (Index 2 → K) //
  Module.finrank K L = 1 ∧ ∀ x ∈ L, splitQuadraticForm K 2 x = 0}
abbrev ThreeExtensions := {M : Submodule K (Index 4 → K) //
  Module.finrank K M = 3 ∧ (∀ x ∈ M, splitQuadraticForm K 4 x = 0) ∧ rootPlane K ≤ M}

def residualMatrixLineEquiv : ResidualSingularLines K ≃ SingularMatrixLines K where
  toFun L := ⟨L.val.map (determinantCoordinates K).toLinearMap,
    ((determinantCoordinates K).finrank_map_eq L.val).trans L.property.1, by
      rintro A ⟨x, hx, rfl⟩
      exact (determinantCoordinates_det K x).trans (L.property.2 x hx)⟩
  invFun M := ⟨M.val.map (determinantCoordinates K).symm.toLinearMap,
    ((determinantCoordinates K).symm.finrank_map_eq M.val).trans M.property.1, by
      rintro x ⟨A, hA, rfl⟩
      have hh := determinantCoordinates_det K ((determinantCoordinates K).symm A)
      rw [LinearEquiv.apply_symm_apply] at hh
      exact hh.symm.trans (M.property.2 A hA)⟩
  left_inv L := Subtype.ext ((Submodule.map_symm_eq_iff (determinantCoordinates K)).mpr rfl)
  right_inv M := Subtype.ext ((Submodule.map_symm_eq_iff (determinantCoordinates K).symm).mpr rfl)

def extendResidualLine (L : ResidualSingularLines K) : ThreeExtensions K :=
  ⟨extension K L.val, by rw [extension_finrank, L.property.1],
    extension_singular K L.val L.property.2, rootPlane_le_extension K L.val⟩

def restrictThreeExtension (M : ThreeExtensions K) : ResidualSingularLines K :=
  ⟨restriction K M.val, by
    have hh := extension_finrank K (restriction K M.val)
    rw [extension_restriction_eq K M.val M.property.2.1 M.property.2.2, M.property.1] at hh
    omega, restriction_singular K M.val M.property.2.1 M.property.2.2⟩

def residualThreeEquiv : ResidualSingularLines K ≃ ThreeExtensions K where
  toFun := extendResidualLine K
  invFun := restrictThreeExtension K
  left_inv L := Subtype.ext (restriction_extension_eq K L.val)
  right_inv M := Subtype.ext (extension_restriction_eq K M.val M.property.2.1 M.property.2.2)

def threeExtensionRulingEquiv : RulingParameters K × RulingParameters K ≃ ThreeExtensions K :=
  (segreLineEquiv K).trans ((residualMatrixLineEquiv K).symm.trans (residualThreeEquiv K))

theorem threeExtensionRuling_intersection (p q : RulingParameters K) :
    (threeExtensionRulingEquiv K (p, q)).val =
      (columnMaximalExtension K p).val ⊓ (rowMaximalExtension K q).val := by
  have hres : originalColumnPlane K p.rep ⊓ originalRowPlane K q.rep =
      (Submodule.span K {columnMap K p.rep q.rep}).map (determinantCoordinates K).symm.toLinearMap := by
    change (columnPlane K p.rep).map (determinantCoordinates K).symm.toLinearMap ⊓
      (rowPlane K q.rep).map (determinantCoordinates K).symm.toLinearMap = _
    rw [← Submodule.map_inf _ (determinantCoordinates K).symm.injective,
      column_inf_row_eq_span K p.rep q.rep p.rep_nonzero]
  change extension K ((Submodule.span K {columnMap K p.rep q.rep}).map
      (determinantCoordinates K).symm.toLinearMap) =
    extension K (originalColumnPlane K p.rep) ⊓ extension K (originalRowPlane K q.rep)
  rw [← extension_inf, hres]

theorem threeExtension_card [Finite K] : Nat.card (ThreeExtensions K) = (Nat.card K + 1) ^ 2 := by
  rw [Nat.card_congr (threeExtensionRulingEquiv K).symm, Nat.card_prod, rulingParameter_card]
  ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
