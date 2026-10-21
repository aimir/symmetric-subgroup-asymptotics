import SymmetricSubgroupAsymptotics.S8Seed18OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed18LowCanonical1
import SymmetricSubgroupAsymptotics.S8Seed18LowCanonical2
import SymmetricSubgroupAsymptotics.S8Seed18LowCanonical3
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8LargerBinarySeedCanonicalCoverage

/-! Exact canonical action coverage above original8T18. The three low
bindings use their actual point permutations and bidirectional words;
all other cases retain an actual larger binary subgroup of the source. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed18CanonicalCoverage
open S8Seed18LeftCosets S8Seed18LowModels

private theorem low_canonical (U : Subgroup Ambient) (hnot : ¬ IsPGroup 2 U)
    (i : Fin 4) (d : Ambient) (hd : MulAut.conj d • U = rows i) :
    ∃ j : Fin 24, ∃ c : Ambient,
      MulAut.conj c • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  fin_cases i
  · have hc : MulAut.conj d • U = H := hd.trans rows_zero
    exact False.elim (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U H d hc
      S8Seed18OvergroupCoverage.seed_isPGroup))
  · refine ⟨4, S8Seed18LowCanonical1.conjugator * d, ?_⟩
    rw [map_mul, mul_smul, hd]
    exact S8Seed18LowCanonical1.exact_eq
  · refine ⟨3, S8Seed18LowCanonical2.conjugator * d, ?_⟩
    rw [map_mul, mul_smul, hd]
    exact S8Seed18LowCanonical2.exact_eq
  · refine ⟨2, S8Seed18LowCanonical3.conjugator * d, ?_⟩
    rw [map_mul, mul_smul, hd]
    exact S8Seed18LowCanonical3.exact_eq

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    ∃ i : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical i := by
  rcases S8Seed18OvergroupCoverage.complete_of_conjugate U Q hQU c hc with
    ⟨i, d, hd⟩ | ⟨P, hPU, hp, ht, hcard⟩
  · exact low_canonical U hnot i d hd
  · exact S8LargerBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed18CanonicalCoverage
end
