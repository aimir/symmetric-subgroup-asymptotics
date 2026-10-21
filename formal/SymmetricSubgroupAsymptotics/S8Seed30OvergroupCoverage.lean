import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.SeedAdjunctionLargerSubgroup
import SymmetricSubgroupAsymptotics.S8Sylow128OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed30Root1Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root2Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root3Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root4Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root5Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root6Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root7Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root8Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root9Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root10Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root11Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root12Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root13Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root14Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root15Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root16Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root17Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root18Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root19Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root20Contains128
import SymmetricSubgroupAsymptotics.S8Seed30Root21Contains128

/-! Complete overgroup reduction above original8T30. The630-coset cover,
22-root normalizer forest and21 literal ordinary-word inclusions show that
every strict adjunction contains an actual conjugate of original8T35.
Every proper overgroup therefore uses the already checked H128 classifier.
No finite catalogue classification is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed30OvergroupCoverage
open S8Seed30LeftCosets FiniteSubgroupAdjunctionCoverage

abbrev LargerSeed : Subgroup Ambient := S8Sylow128LeftCosets.H

theorem root_property (k : Fin 22) : EqSeedOrContainsConjugate H LargerSeed
    (H ⊔ Subgroup.closure {representatives (S8Seed30NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact Or.inl S8Seed30NormalizerRoots.root_zero_eq_seed
  · exact Or.inr ⟨S8Seed30Root1Contains128.conjugator, S8Seed30Root1Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root2Contains128.conjugator, S8Seed30Root2Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root3Contains128.conjugator, S8Seed30Root3Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root4Contains128.conjugator, S8Seed30Root4Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root5Contains128.conjugator, S8Seed30Root5Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root6Contains128.conjugator, S8Seed30Root6Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root7Contains128.conjugator, S8Seed30Root7Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root8Contains128.conjugator, S8Seed30Root8Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root9Contains128.conjugator, S8Seed30Root9Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root10Contains128.conjugator, S8Seed30Root10Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root11Contains128.conjugator, S8Seed30Root11Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root12Contains128.conjugator, S8Seed30Root12Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root13Contains128.conjugator, S8Seed30Root13Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root14Contains128.conjugator, S8Seed30Root14Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root15Contains128.conjugator, S8Seed30Root15Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root16Contains128.conjugator, S8Seed30Root16Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root17Contains128.conjugator, S8Seed30Root17Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root18Contains128.conjugator, S8Seed30Root18Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root19Contains128.conjugator, S8Seed30Root19Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root20Contains128.conjugator, S8Seed30Root20Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed30Root21Contains128.conjugator, S8Seed30Root21Contains128.contains_seed⟩

theorem strict_adjoin_contains (g : Ambient) (hg : g ∉ H) :
    ∃ c : Ambient, MulAut.conj c • LargerSeed ≤ H ⊔ Subgroup.closure {g} :=
  strict_adjoin_contains_of_forest S8Seed30LeftCosets.certificate
    S8Seed30NormalizerRoots.reduction SymmetricEightTwoGenerators.generators_full
    root_property g hg

theorem eq_seed_or_contains (U : Subgroup Ambient) (hHU : H ≤ U) :
    U = H ∨ ∃ c : Ambient, MulAut.conj c • LargerSeed ≤ U := by
  classical
  by_cases heq : U = H
  · exact Or.inl heq
  · right
    have hnot : ¬ U ≤ H := fun h => heq (le_antisymm h hHU)
    obtain ⟨g, hgU, hgH⟩ := Set.not_subset.mp hnot
    obtain ⟨c, hc⟩ := strict_adjoin_contains g hgH
    refine ⟨c, hc.trans (sup_le hHU ?_)⟩
    apply (Subgroup.closure_le U).mpr
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact hgU

/-- Every proper actual overgroup of this order64 seed is covered by the
previous H128 classification; the remaining case is the actual seed. -/
theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) :
    U = H ∨ Covered S8Sylow128SelectedRows.rows U := by
  rcases eq_seed_or_contains U hHU with heq | ⟨c, hc⟩
  · exact Or.inl heq
  · right
    have hmap : MulAut.conj c⁻¹ • (MulAut.conj c • LargerSeed) ≤
        MulAut.conj c⁻¹ • U := by
      change (MulAut.conj c • LargerSeed).map (MulAut.conj c⁻¹).toMonoidHom ≤
        U.map (MulAut.conj c⁻¹).toMonoidHom
      exact Subgroup.map_mono hc
    have hlarge : LargerSeed ≤ MulAut.conj c⁻¹ • U := by
      simpa only [map_inv, inv_smul_smul] using hmap
    obtain ⟨i, d, hd⟩ := S8Sylow128OvergroupCoverage.complete _ hlarge
    refine ⟨i, d * c⁻¹, ?_⟩
    rw [map_mul, mul_smul, hd]

/-- Point-conjugate source charts are transported by the same ambient
permutations. No abstract isomorphism is substituted for the action. -/
theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) :
    U = Q ∨ Covered S8Sylow128SelectedRows.rows U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with heq | ⟨i, d, hd⟩
  · left
    have hsame : MulAut.conj c • U = MulAut.conj c • Q := heq.trans hc.symm
    have h := congrArg (fun W : Subgroup Ambient => MulAut.conj c⁻¹ • W) hsame
    simpa only [map_inv, inv_smul_smul] using h
  · right
    refine ⟨i, d * c, ?_⟩
    rw [map_mul, mul_smul, hd]

theorem seed_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 6) (by
    change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T30.generators)) = 64
    exact BinaryMenuCayley8T30.exact_card)

/-- Exact fixed-catalogue point coverage for every nonbinary overgroup. -/
theorem canonical_complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    ∃ j : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  rcases complete_of_conjugate U Q hQU c hc with heq | hlarge
  · have hp : IsPGroup 2 U := by
      rw [heq]
      exact S8CanonicalNonbinaryTransport.isPGroup_of_conjugate Q H c hc seed_isPGroup
    exact False.elim (hnot hp)
  · exact S8CanonicalNonbinaryTransport.of_large_covered U hnot hlarge

end SymmetricSubgroupAsymptotics.S8Seed30OvergroupCoverage
end
