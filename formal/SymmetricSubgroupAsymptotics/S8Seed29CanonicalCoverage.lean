import SymmetricSubgroupAsymptotics.S8Seed29OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8Seed29LowCanonical1
import SymmetricSubgroupAsymptotics.S8Seed29LowCanonical2
import SymmetricSubgroupAsymptotics.S8Seed29LowCanonical3
import SymmetricSubgroupAsymptotics.S8Seed29LowCanonical4
import SymmetricSubgroupAsymptotics.S8Seed29LowCanonical5

/-! Canonical point-action coverage of every nonbinary actual overgroup
of the original8T29 seed. The five direct point bindings cover the two
other low models by the actual selected normalizer. The remaining low
model is the checked binary seed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29CanonicalCoverage
open S8Seed29LeftCosets S8Seed29LowModels
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem low_seed_isPGroup : IsPGroup 2 (rows 0) := by
  rw [rows_zero]
  apply IsPGroup.of_card (n := 6)
  change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T29.generators)) = 64
  exact BinaryMenuCayley8T29.exact_card

theorem model_canonical (i : Fin 8) (hi : i ≠ 0) :
    ∃ j : Fin 24, ∃ c : S8Seed29LeftCosets.Ambient,
      MulAut.conj c • rows i = DegreeEightCanonicalCatalogue.canonical j := by
  fin_cases i
  · exact False.elim (hi rfl)
  · exact ⟨19, S8Seed29LowCanonical1.conjugator, S8Seed29LowCanonical1.exact_eq⟩
  · exact ⟨22, S8Seed29LowCanonical2.conjugator, S8Seed29LowCanonical2.exact_eq⟩
  · exact ⟨7, S8Seed29LowCanonical3.conjugator, S8Seed29LowCanonical3.exact_eq⟩
  · exact ⟨6, S8Seed29LowCanonical4.conjugator, S8Seed29LowCanonical4.exact_eq⟩
  · exact ⟨14, S8Seed29LowCanonical5.conjugator, S8Seed29LowCanonical5.exact_eq⟩
  · refine ⟨19, S8Seed29LowCanonical1.conjugator * S8Seed29NormalizerRoots.normalizer, ?_⟩
    change MulAut.conj (S8Seed29LowCanonical1.conjugator * S8Seed29NormalizerRoots.normalizer) •
      rows 6 = DegreeEightCanonicalCatalogue.canonical 19
    rw [map_mul, mul_smul, S8Seed29LowConjugacy.conjugates_row6]
    exact S8Seed29LowCanonical1.exact_eq
  · refine ⟨6, S8Seed29LowCanonical4.conjugator * S8Seed29NormalizerRoots.normalizer, ?_⟩
    change MulAut.conj (S8Seed29LowCanonical4.conjugator * S8Seed29NormalizerRoots.normalizer) •
      rows 7 = DegreeEightCanonicalCatalogue.canonical 6
    rw [map_mul, mul_smul, S8Seed29LowConjugacy.conjugates_row7]
    exact S8Seed29LowCanonical4.exact_eq

theorem of_low_conjugate (U : Subgroup S8Seed29LeftCosets.Ambient) (hnot : ¬ IsPGroup 2 U)
    (i : Fin 8) (c : S8Seed29LeftCosets.Ambient) (hc : MulAut.conj c • U = rows i) :
    ∃ j : Fin 24, ∃ d : S8Seed29LeftCosets.Ambient,
      MulAut.conj d • U = DegreeEightCanonicalCatalogue.canonical j := by
  by_cases hi : i = 0
  · subst i
    exact False.elim (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate
      U _ c hc low_seed_isPGroup))
  · obtain ⟨j, d, hd⟩ := model_canonical i hi
    refine ⟨j, d * c, ?_⟩
    rw [map_mul, mul_smul, hc, hd]

/-- The actual point chart of any contained conjugate seed suffices.
No action classification hypothesis is retained. -/
theorem complete_of_conjugate (U Q : Subgroup S8Seed29LeftCosets.Ambient) (hQU : Q ≤ U)
    (c : S8Seed29LeftCosets.Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    ∃ j : Fin 24, ∃ d : S8Seed29LeftCosets.Ambient,
      MulAut.conj d • U = DegreeEightCanonicalCatalogue.canonical j := by
  rcases S8Seed29OvergroupCoverage.complete_of_conjugate U Q hQU c hc with
    ⟨i, d, hd⟩ | hlarge
  · exact of_low_conjugate U hnot i d hd
  · exact S8CanonicalNonbinaryTransport.of_large_covered U hnot hlarge

end SymmetricSubgroupAsymptotics.S8Seed29CanonicalCoverage
end
