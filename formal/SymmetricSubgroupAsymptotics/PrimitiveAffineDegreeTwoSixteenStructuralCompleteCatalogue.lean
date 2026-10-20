import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoZeroSixteenStructuralFinitePackages
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoSixteenInstalledSocles

/-! Complete the exact original sixty-four one-frame callbacks. The two
new families are structural proofs with the same published parameters. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoSixteenStructuralCompleteCatalogue

private theorem missingZero_last_two (j : Fin 29)
    (hmissing : j ∉ DegreeTwoSixteenInstalledSocles.installedZero) :
    j = (27 : Fin 29) ∨ j = (28 : Fin 29) := by
  have he : DegreeTwoSixteenInstalledSocles.installedZero =
      Finset.univ.filter (fun i : Fin 29 => i.val < 27) := by decide +kernel
  have hlarge : ¬ j.val < 27 := by
    intro hj
    apply hmissing
    rw [he]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j,hj⟩
  have hv : j.val = 27 ∨ j.val = 28 := by omega
  rcases hv with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

/-- Precisely the two original missing zero16 families. -/
def remainingData (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    DegreeTwoSixteenInstalledSocles.RemainingData where
  zero16 j hmissing := by
    have hj := missingZero_last_two j hmissing
    classical
    by_cases hj27 : j = (27 : Fin 29)
    · subst j
      exact PrimitiveAffineDegreeTwoZeroSixteenStructuralFinitePackages.Row28.family socle hMN
    · have hj28 := hj.resolve_left hj27
      subst j
      exact PrimitiveAffineDegreeTwoZeroSixteenStructuralFinitePackages.Row29.family socle hMN

/-- This supplies the existing complete one-frame catalogue interface. -/
def finiteCatalogue (socle : PublishedPrimitiveSocleDichotomyInput)
    (hMN : McIverNeumannPermutationGeneratorBound) :
    DegreeTwoSixteenOneFrameFiniteRows.Catalogue.DegreeTwoSixteenOneFrameFiniteCatalogueData :=
  (remainingData socle hMN).finiteCatalogue

end DegreeTwoSixteenStructuralCompleteCatalogue
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
