import SymmetricSubgroupAsymptotics.S8Seed6OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed6LowRoot37Canonical
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8AboveSixteenBinarySeedCanonicalCoverage

/-! Exact actual-point canonical coverage above original8T6. The two low
rows use one literal Top22 binding and the proved normalizer interchange. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed6CanonicalCoverage
open S8Seed6LeftCosets S8Seed6LowModels

theorem low_one_canonical :
    MulAut.conj S8Seed6LowRoot37Canonical.conjugator • rows 1 =
      PrimitiveAffineEightTop22CatalogueBinding.catalogueAction := by
  change MulAut.conj S8Seed6LowRoot37Canonical.conjugator •
    S8Seed6LowRoot37Canonical.lowRow = _
  exact S8Seed6LowRoot37Canonical.canonical_conjugated

theorem low_two_canonical :
    MulAut.conj (S8Seed6LowRoot37Canonical.conjugator * S8Seed6NormalizerRoots.normalizer⁻¹) • rows 2 =
      PrimitiveAffineEightTop22CatalogueBinding.catalogueAction := by
  rw [map_mul, mul_smul, S8Seed6LowRelations.inverse_normalizer_two]
  exact low_one_canonical

private theorem low_canonical (U : Subgroup Ambient) (hnot : ¬ IsPGroup 2 U)
    (i : Fin 3) (d : Ambient) (hd : MulAut.conj d • U = rows i) :
    ∃ j : Fin 24, ∃ c : Ambient,
      MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  fin_cases i
  · have hc : MulAut.conj d • U = H := hd.trans rows_zero
    exact False.elim (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U H d hc
      S8Seed6OvergroupCoverage.seed_isPGroup))
  · refine ⟨21, S8Seed6LowRoot37Canonical.conjugator * d, ?_⟩
    rw [map_mul, mul_smul, hd]
    exact low_one_canonical
  · refine ⟨21, (S8Seed6LowRoot37Canonical.conjugator * S8Seed6NormalizerRoots.normalizer⁻¹) * d, ?_⟩
    rw [map_mul, mul_smul, hd]
    exact low_two_canonical

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  rcases S8Seed6OvergroupCoverage.complete_of_conjugate U Q hQU c hc with
    ⟨i, d, hd⟩ | ⟨P, hPU, hp, ht, hcard⟩
  · exact low_canonical U hnot i d hd
  · exact S8AboveSixteenBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed6CanonicalCoverage
end
