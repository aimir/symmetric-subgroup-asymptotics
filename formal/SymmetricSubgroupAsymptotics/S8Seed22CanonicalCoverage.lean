import SymmetricSubgroupAsymptotics.S8Seed22OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8LargerBinarySeedCanonicalCoverage

/-! Exact canonical point coverage above original8T22. The low row uses
its literal Top12 point binding; the high branch retains its actual
larger transitive binary subgroup and its inclusion in the source. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed22CanonicalCoverage
open S8Seed22LeftCosets S8Seed22OvergroupCoverage

private theorem low_canonical (U : Subgroup Ambient) (hnot : ¬ IsPGroup 2 U)
    (i : Fin 2) (d : Ambient) (hd : MulAut.conj d • U = lowRows i) :
    ∃ j : Fin 24, ∃ c : Ambient,
      MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  fin_cases i
  · have hc : MulAut.conj d • U = H := hd
    exact False.elim (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U H d hc
      S8Seed22OvergroupCoverage.seed_isPGroup))
  · refine ⟨11, S8Seed22LowRowPilot.conjugator * d, ?_⟩
    rw [map_mul, mul_smul, hd]
    exact S8Seed22LowRowPilot.canonical_conjugated

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  rcases S8Seed22OvergroupCoverage.complete_of_conjugate U Q hQU c hc with
    ⟨i, d, hd⟩ | ⟨P, hPU, hp, ht, hcard⟩
  · exact low_canonical U hnot i d hd
  · exact S8LargerBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed22CanonicalCoverage
end
