import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.S8Seed27OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed28OvergroupCoverage

/-! Fixed-catalogue point coverage from the previously completed128,
original8T27 and original8T28 seeds. The contained source subgroup and
its ambient point chart are retained explicitly in each theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.S8CompletedHigherSeedCanonicalCoverage
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

abbrev Ambient := Equiv.Perm (Fin 8)

theorem seed128 (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = S8Sylow128LeftCosets.H)
    (hnot : ¬ IsPGroup 2 U) : ∃ i : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = DegreeEightCanonicalCatalogue.canonical i := by
  have hHU : S8Sylow128LeftCosets.H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  obtain ⟨i, d, hd⟩ := S8Sylow128OvergroupCoverage.complete _ hHU
  apply S8CanonicalNonbinaryTransport.of_large_covered U hnot
  refine ⟨i, d * c, ?_⟩
  rw [map_mul, mul_smul, hd]

private theorem seed27_binary : IsPGroup 2 S8Seed27LeftCosets.H :=
  IsPGroup.of_card (n := 6) (by
    change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)) = 64
    exact BinaryMenuCayley8T27.exact_card)

theorem seed27 (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = S8Seed27LeftCosets.H)
    (hnot : ¬ IsPGroup 2 U) : ∃ i : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = DegreeEightCanonicalCatalogue.canonical i := by
  rcases S8Seed27OvergroupCoverage.complete_of_conjugate U Q hQU c hc with heq | hlarge
  · have hp : IsPGroup 2 U := by
      rw [heq]
      exact S8CanonicalNonbinaryTransport.isPGroup_of_conjugate Q _ c hc seed27_binary
    exact False.elim (hnot hp)
  · exact S8CanonicalNonbinaryTransport.of_large_covered U hnot hlarge

private theorem seed28_binary : IsPGroup 2 S8Seed28LeftCosets.H :=
  IsPGroup.of_card (n := 6) (by
    change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T28.generators)) = 64
    exact BinaryMenuCayley8T28.exact_card)

theorem seed28 (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = S8Seed28LeftCosets.H)
    (hnot : ¬ IsPGroup 2 U) : ∃ i : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = DegreeEightCanonicalCatalogue.canonical i := by
  rcases S8Seed28OvergroupCoverage.complete_of_conjugate U Q hQU c hc with
    heq | ⟨d, hd⟩ | hlarge
  · have hp : IsPGroup 2 U := by
      rw [heq]
      exact S8CanonicalNonbinaryTransport.isPGroup_of_conjugate Q _ c hc seed28_binary
    exact False.elim (hnot hp)
  · refine ⟨8, S8Seed28LowRowPilot.conjugator * d, ?_⟩
    rw [map_mul, mul_smul, hd]
    exact S8Seed28LowRowPilot.canonical_conjugated
  · exact S8CanonicalNonbinaryTransport.of_large_covered U hnot hlarge

end SymmetricSubgroupAsymptotics.S8CompletedHigherSeedCanonicalCoverage

end
