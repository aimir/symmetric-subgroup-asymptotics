import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualCorrespondence
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD2Rulings

/-! Actual original maximal Q-singular D4 extensions of the fixed
root plane are EXACTLY the two residual PG1 families. The displayed
equivalence retains original coordinates, inclusion and quadratic zero.
Matching these families with the genuine global parity components and
recognizing the intrinsic local graph are subsequent obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexBundledQuadratic
open CFSGOrthogonalDIndexTrialityD2Coordinates
variable (K : Type) [Field K]

abbrev MaximalExtensions := {M : Submodule K (Index 4 → K) //
  Module.finrank K M = 4 ∧ (∀ x ∈ M, splitQuadraticForm K 4 x = 0) ∧ rootPlane K ≤ M}

def extendResidualPlane (L : ResidualSingularPlanes K) : MaximalExtensions K :=
  ⟨extension K L.val, by rw [extension_finrank, L.property.1],
    extension_singular K L.val L.property.2, rootPlane_le_extension K L.val⟩

def restrictMaximalExtension (M : MaximalExtensions K) : ResidualSingularPlanes K :=
  ⟨restriction K M.val, restriction_finrank_of_four K M.val M.property.1 M.property.2.1 M.property.2.2,
    restriction_singular K M.val M.property.2.1 M.property.2.2⟩

def residualExtensionEquiv : ResidualSingularPlanes K ≃ MaximalExtensions K where
  toFun := extendResidualPlane K
  invFun := restrictMaximalExtension K
  left_inv L := Subtype.ext (restriction_extension_eq K L.val)
  right_inv M := Subtype.ext (extension_restriction_eq K M.val M.property.2.1 M.property.2.2)

def maximalExtensionRulingEquiv :
    RulingParameters K ⊕ RulingParameters K ≃ MaximalExtensions K :=
  (rulingEquiv K).trans (residualExtensionEquiv K)

def columnMaximalExtension (p : RulingParameters K) : MaximalExtensions K :=
  extendResidualPlane K (columnRuling K p)

def rowMaximalExtension (p : RulingParameters K) : MaximalExtensions K :=
  extendResidualPlane K (rowRuling K p)

theorem columnMaximalExtension_injective : Function.Injective (columnMaximalExtension K) :=
  (residualExtensionEquiv K).injective.comp (columnRuling_injective K)

theorem rowMaximalExtension_injective : Function.Injective (rowMaximalExtension K) :=
  (residualExtensionEquiv K).injective.comp (rowRuling_injective K)

theorem columnMaximalExtension_ne_rowMaximalExtension (p q : RulingParameters K) :
    columnMaximalExtension K p ≠ rowMaximalExtension K q := by
  intro he
  exact columnRuling_ne_rowRuling K p q ((residualExtensionEquiv K).injective he)

theorem maximalExtension_card [Finite K] : Nat.card (MaximalExtensions K) = 2 * (Nat.card K + 1) :=
  (Nat.card_congr (residualExtensionEquiv K).symm).trans (residualSingularPlane_card K)

theorem columnMaximalExtension_range_card [Finite K] :
    Nat.card (Set.range (columnMaximalExtension K)) = Nat.card K + 1 :=
  (Nat.card_range_of_injective (columnMaximalExtension_injective K)).trans (rulingParameter_card K)

theorem rowMaximalExtension_range_card [Finite K] :
    Nat.card (Set.range (rowMaximalExtension K)) = Nat.card K + 1 :=
  (Nat.card_range_of_injective (rowMaximalExtension_injective K)).trans (rulingParameter_card K)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
