import SymmetricSubgroupAsymptotics.S8Seed9OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed9LowRoot8Canonical
import SymmetricSubgroupAsymptotics.S8Seed9LowRoot37Canonical
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8AboveSixteenBinarySeedCanonicalCoverage

/-! Point charts for both literal low roots are supplied by actual
bidirectional ordinary words. Normalizer conjugates retain those charts.
No canonical correspondence is inferred from the low group orders. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed9CanonicalCoverage
open S8Seed9LeftCosets S8Seed9LowModels

private theorem low_one_match :
    ∃ j : Fin 24, ∃ c : Ambient, MulAut.conj c • rows 1 =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  exact ⟨5, S8Seed9LowRoot8Canonical.conjugator,
    S8Seed9LowRoot8Canonical.canonical_conjugated⟩

private theorem low_two_match :
    ∃ j : Fin 24, ∃ c : Ambient, MulAut.conj c • rows 2 =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  exact ⟨5, S8Seed9LowRoot37Canonical.conjugator,
    S8Seed9LowRoot37Canonical.canonical_conjugated⟩

private theorem low_three_match :
    ∃ j : Fin 24, ∃ c : Ambient, MulAut.conj c • rows 3 =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  obtain ⟨j,c,hc⟩ := low_one_match
  refine ⟨j,c*S8Seed9NormalizerRoots.normalizer⁻¹,?_⟩
  rw [map_mul,mul_smul,S8Seed9LowRelations.inverse_normalizer_three]
  exact hc

private theorem low_four_match :
    ∃ j : Fin 24, ∃ c : Ambient, MulAut.conj c • rows 4 =
      Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  obtain ⟨j,c,hc⟩ := low_two_match
  refine ⟨j,c*S8Seed9NormalizerRoots.normalizer⁻¹,?_⟩
  rw [map_mul,mul_smul,S8Seed9LowRelations.inverse_normalizer_four]
  exact hc

private theorem seed_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 4) BinaryMenuCayley8T9.exact_card

private theorem low_canonical (U : Subgroup Ambient) (hnot : ¬IsPGroup 2 U)
    (i : Fin 5) (d : Ambient) (hd : MulAut.conj d • U = rows i) :
    ∃ j : Fin 24,∃ c : Ambient,
      MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  fin_cases i
  · have hc : MulAut.conj d • U = H := hd.trans rows_zero
    exact (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U H d hc seed_isPGroup)).elim
  · obtain ⟨j,c,hc⟩ := low_one_match
    refine ⟨j,c*d,?_⟩
    rw [map_mul,mul_smul,hd]
    exact hc
  · obtain ⟨j,c,hc⟩ := low_two_match
    refine ⟨j,c*d,?_⟩
    rw [map_mul,mul_smul,hd]
    exact hc
  · obtain ⟨j,c,hc⟩ := low_three_match
    refine ⟨j,c*d,?_⟩
    rw [map_mul,mul_smul,hd]
    exact hc
  · obtain ⟨j,c,hc⟩ := low_four_match
    refine ⟨j,c*d,?_⟩
    rw [map_mul,mul_smul,hd]
    exact hc

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬IsPGroup 2 U) :
    ∃ i : Fin 24,∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  rcases S8Seed9OvergroupCoverage.low_or_escape_of_conjugate U Q hQU c hc with
    ⟨i,d,hd⟩ | ⟨P,hPU,hp,ht,hcard⟩
  · exact low_canonical U hnot i d hd
  · exact S8AboveSixteenBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed9CanonicalCoverage
end
