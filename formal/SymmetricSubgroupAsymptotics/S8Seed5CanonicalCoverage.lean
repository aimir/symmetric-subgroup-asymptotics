import SymmetricSubgroupAsymptotics.S8Seed5OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed5LowRoot161Canonical
import SymmetricSubgroupAsymptotics.S8Seed5LowRoot372Canonical
import SymmetricSubgroupAsymptotics.S8CanonicalPointCharts
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8AboveEightBinarySeedCanonicalCoverage

/-! Two literal low representatives have actual canonical point charts.
The other two are retained normalizer images, with charts composed on the
original eight points. No abstract-order correspondence is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed5CanonicalCoverage
open S8Seed5LeftCosets S8Seed5LowModels

private theorem match1 : S8CanonicalPointCharts.Has (rows 1) := by
  refine ⟨10, S8Seed5LowRoot161Canonical.conjugator, ?_⟩
  rw [←S8Seed5LowRoot161Row.root_row]
  exact S8Seed5LowRoot161Canonical.canonical_conjugated

private theorem match3 : S8CanonicalPointCharts.Has (rows 3) := by
  refine ⟨10, S8Seed5LowRoot372Canonical.conjugator, ?_⟩
  rw [←S8Seed5LowRoot372Row.root_row]
  exact S8Seed5LowRoot372Canonical.canonical_conjugated

private theorem match2 : S8CanonicalPointCharts.Has (rows 2) :=
  S8Seed5LowNormalizer1.normalizer_image ▸
    S8CanonicalPointCharts.conjugated (rows 1) S8Seed5NormalizerRoots.normalizer match1

private theorem match4 : S8CanonicalPointCharts.Has (rows 4) :=
  S8Seed5LowNormalizer3.normalizer_image ▸
    S8CanonicalPointCharts.conjugated (rows 3) S8Seed5NormalizerRoots.normalizer match3

private theorem low_binary_or_chart (i : Fin 5) :
    IsPGroup 2 (rows i) ∨ S8CanonicalPointCharts.Has (rows i) := by
  fin_cases i
  · left
    change IsPGroup 2 (rows 0)
    rw [rows_zero]
    exact IsPGroup.of_card (n := 3) BinaryMenuCayley8T5.exact_card
  · exact Or.inr match1
  · exact Or.inr match2
  · exact Or.inr match3
  · exact Or.inr match4

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    S8CanonicalPointCharts.Has U := by
  rcases S8Seed5OvergroupCoverage.low_or_escape_of_conjugate U Q hQU c hc with
    ⟨i, d, hd⟩ | ⟨P, hPU, hp, ht, hcard⟩
  · rcases low_binary_or_chart i with hbinary | hchart
    · exact (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U _ d hd hbinary)).elim
    · exact S8CanonicalPointCharts.of_conjugate U _ d hd hchart
  · exact S8AboveEightBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed5CanonicalCoverage
end
