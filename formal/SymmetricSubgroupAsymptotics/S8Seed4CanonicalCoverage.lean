import SymmetricSubgroupAsymptotics.S8Seed4OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed4LowRoot46Canonical
import SymmetricSubgroupAsymptotics.S8Seed4LowRoot160Canonical
import SymmetricSubgroupAsymptotics.S8Seed4LowRoot225Canonical
import SymmetricSubgroupAsymptotics.S8Seed4LowRoot226Canonical
import SymmetricSubgroupAsymptotics.S8Seed4LowRoot440Canonical
import SymmetricSubgroupAsymptotics.S8CanonicalPointCharts
import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8AboveEightBinarySeedCanonicalCoverage

/-! Exact point matching for the five literal low representatives.
Additional low rows are actual normalizer images. Every displayed chart
is an imported bidirectional word proof, never a match inferred from order. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed4CanonicalCoverage
open S8Seed4LeftCosets S8Seed4LowModels

private theorem match1 : S8CanonicalPointCharts.Has (rows 1) := by
  refine ⟨20, S8Seed4LowRoot46Canonical.conjugator, ?_⟩
  rw [←S8Seed4LowRoot46Row.root_row]
  exact S8Seed4LowRoot46Canonical.canonical_conjugated

private theorem match2 : S8CanonicalPointCharts.Has (rows 2) := by
  refine ⟨1, S8Seed4LowRoot160Canonical.conjugator, ?_⟩
  rw [←S8Seed4LowRoot160Row.root_row]
  exact S8Seed4LowRoot160Canonical.canonical_conjugated

private theorem match3 : S8CanonicalPointCharts.Has (rows 3) := by
  refine ⟨20, S8Seed4LowRoot225Canonical.conjugator, ?_⟩
  rw [←S8Seed4LowRoot225Row.root_row]
  exact S8Seed4LowRoot225Canonical.canonical_conjugated

private theorem match4 : S8CanonicalPointCharts.Has (rows 4) := by
  refine ⟨1, S8Seed4LowRoot226Canonical.conjugator, ?_⟩
  rw [←S8Seed4LowRoot226Row.root_row]
  exact S8Seed4LowRoot226Canonical.canonical_conjugated

private theorem match6 : S8CanonicalPointCharts.Has (rows 6) := by
  refine ⟨1, S8Seed4LowRoot440Canonical.conjugator, ?_⟩
  rw [←S8Seed4LowRoot440Row.root_row]
  exact S8Seed4LowRoot440Canonical.canonical_conjugated

private theorem match5 : S8CanonicalPointCharts.Has (rows 5) :=
  S8Seed4LowNormalizer3.normalizer_image ▸
    S8CanonicalPointCharts.conjugated (rows 3) S8Seed4NormalizerRoots.normalizer match3

private theorem match7 : S8CanonicalPointCharts.Has (rows 7) :=
  S8Seed4LowNormalizer1.normalizer_image ▸
    S8CanonicalPointCharts.conjugated (rows 1) S8Seed4NormalizerRoots.normalizer match1

private theorem match8 : S8CanonicalPointCharts.Has (rows 8) :=
  S8Seed4LowNormalizer4.normalizer_image ▸
    S8CanonicalPointCharts.conjugated (rows 4) S8Seed4NormalizerRoots.normalizer match4

private theorem low_binary_or_chart (i : Fin 9) :
    IsPGroup 2 (rows i) ∨ S8CanonicalPointCharts.Has (rows i) := by
  fin_cases i
  · left
    change IsPGroup 2 (rows 0)
    rw [rows_zero]
    exact IsPGroup.of_card (n := 3) BinaryMenuCayley8T4.exact_card
  · exact Or.inr match1
  · exact Or.inr match2
  · exact Or.inr match3
  · exact Or.inr match4
  · exact Or.inr match5
  · exact Or.inr match6
  · exact Or.inr match7
  · exact Or.inr match8

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    S8CanonicalPointCharts.Has U := by
  rcases S8Seed4OvergroupCoverage.low_or_escape_of_conjugate U Q hQU c hc with
    ⟨i, d, hd⟩ | ⟨P, hPU, hp, ht, hcard⟩
  · rcases low_binary_or_chart i with hbinary | hchart
    · exact (hnot (S8CanonicalNonbinaryTransport.isPGroup_of_conjugate U _ d hd hbinary)).elim
    · exact S8CanonicalPointCharts.of_conjugate U _ d hd hchart
  · exact S8AboveEightBinarySeedCanonicalCoverage.complete U P hPU hp ht hcard hnot

end SymmetricSubgroupAsymptotics.S8Seed4CanonicalCoverage
end
