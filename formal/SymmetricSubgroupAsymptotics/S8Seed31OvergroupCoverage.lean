import SymmetricSubgroupAsymptotics.S8CanonicalNonbinaryTransport
import SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapeCoverage
import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionEdgeProperty
import SymmetricSubgroupAsymptotics.S8Sylow128OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed31LowRowPilot
import SymmetricSubgroupAsymptotics.S8Seed31Root1Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root2Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root3Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root4Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root5Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root6Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root7Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root8Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root9Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root10Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root11Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root12Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root13Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root14Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root15Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root17Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root18Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root19Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root20Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root21Contains128
import SymmetricSubgroupAsymptotics.S8Seed31Root22Contains128

/-! Actual overgroups of original8T31. The unique low root adjoins one
literal subgroup fixed by every selected forest conjugator. All other
nontrivial roots contain an actual conjugate of original8T35. The two low
rows are nested; no classification or numerical group order is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed31OvergroupCoverage
open S8Seed31LeftCosets FiniteSubgroupAdjunctionCoverage

abbrev LargerSeed : Subgroup Ambient := S8Sylow128LeftCosets.H
abbrev LowRow : Subgroup Ambient := S8Seed31LowRowPilot.lowRow

def lowRows : Fin 2 → Subgroup Ambient := ![H, LowRow]

def LowOrLarger (W : Subgroup Ambient) : Prop :=
  (∃ i : Fin 2, W = lowRows i) ∨
    ∃ c : Ambient, MulAut.conj c • LargerSeed ≤ W

theorem lowRows_contain (i : Fin 2) : H ≤ lowRows i := by
  fin_cases i
  · exact le_rfl
  · exact S8Seed31LowRowPilot.seed_le_low

theorem edge_fixes_low (j : Fin 4) (i : Fin 2) :
    MulAut.conj (S8Seed31NormalizerRoots.edgeConjugator j) • lowRows i = lowRows i := by
  fin_cases j
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · fin_cases i
    · exact S8Seed31NormalizerRoots.normalizes_seed
    · exact S8Seed31LowRowPilot.normalizes_low

theorem edge_property (j : Fin 4) (W : Subgroup Ambient) (hW : LowOrLarger W) :
    LowOrLarger (MulAut.conj (S8Seed31NormalizerRoots.edgeConjugator j) • W) := by
  rcases hW with ⟨i, rfl⟩ | ⟨d, hd⟩
  · exact Or.inl ⟨i, edge_fixes_low j i⟩
  · right
    let c := S8Seed31NormalizerRoots.edgeConjugator j
    refine ⟨c * d, ?_⟩
    have hmap : MulAut.conj c • (MulAut.conj d • LargerSeed) ≤
        MulAut.conj c • W := by
      change (MulAut.conj d • LargerSeed).map (MulAut.conj c).toMonoidHom ≤
        W.map (MulAut.conj c).toMonoidHom
      exact Subgroup.map_mono hd
    simpa only [map_mul, mul_smul] using hmap

theorem root_property (k : Fin 23) : LowOrLarger
    (H ⊔ Subgroup.closure {representatives (S8Seed31NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact Or.inl ⟨0, S8Seed31NormalizerRoots.root_zero_eq_seed⟩
  · exact Or.inr ⟨S8Seed31Root1Contains128.conjugator, S8Seed31Root1Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root2Contains128.conjugator, S8Seed31Root2Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root3Contains128.conjugator, S8Seed31Root3Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root4Contains128.conjugator, S8Seed31Root4Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root5Contains128.conjugator, S8Seed31Root5Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root6Contains128.conjugator, S8Seed31Root6Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root7Contains128.conjugator, S8Seed31Root7Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root8Contains128.conjugator, S8Seed31Root8Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root9Contains128.conjugator, S8Seed31Root9Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root10Contains128.conjugator, S8Seed31Root10Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root11Contains128.conjugator, S8Seed31Root11Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root12Contains128.conjugator, S8Seed31Root12Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root13Contains128.conjugator, S8Seed31Root13Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root14Contains128.conjugator, S8Seed31Root14Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root15Contains128.conjugator, S8Seed31Root15Contains128.contains_seed⟩
  · exact Or.inl ⟨1, S8Seed31LowRowPilot.low_eq_adjoin.symm⟩
  · exact Or.inr ⟨S8Seed31Root17Contains128.conjugator, S8Seed31Root17Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root18Contains128.conjugator, S8Seed31Root18Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root19Contains128.conjugator, S8Seed31Root19Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root20Contains128.conjugator, S8Seed31Root20Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root21Contains128.conjugator, S8Seed31Root21Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed31Root22Contains128.conjugator, S8Seed31Root22Contains128.contains_seed⟩

theorem adjoin_property (g : Ambient) : LowOrLarger (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed31LeftCosets.certificate.covers
    SymmetricEightTwoGenerators.generators_full g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (representatives i) hi
  have hp := S8Seed31NormalizerRoots.reduction.edge_property_representative
    LowOrLarger (by
      intro a ha W hW
      change LowOrLarger (MulAut.conj
        (S8Seed31NormalizerRoots.edgeConjugator (S8Seed31NormalizerRoots.letters a)) • W)
      exact edge_property _ W hW) root_property i
  rw [← he] at hp
  exact hp

theorem join_property (i j : Fin 2) : LowOrLarger (lowRows i ⊔ lowRows j) := by
  fin_cases i <;> fin_cases j
  · exact Or.inl ⟨0, sup_idem _⟩
  · exact Or.inl ⟨1, sup_eq_right.mpr S8Seed31LowRowPilot.seed_le_low⟩
  · exact Or.inl ⟨1, sup_eq_left.mpr S8Seed31LowRowPilot.seed_le_low⟩
  · exact Or.inl ⟨1, sup_idem _⟩

theorem low_or_contains (U : Subgroup Ambient) (hHU : H ≤ U) : LowOrLarger U :=
  complete_above_of_seed_joins_or_larger H LargerSeed lowRows lowRows_contain
    ⟨0, rfl⟩ adjoin_property join_property U hHU

/-- Each actual overgroup is the seed, its one low extension, or is
covered by the already checked H128 classification. -/
theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) :
    U = H ∨ U = LowRow ∨ Covered S8Sylow128SelectedRows.rows U := by
  rcases low_or_contains U hHU with ⟨i, hi⟩ | ⟨c, hc⟩
  · fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
  · right; right
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

/-- The low case retains an actual point conjugator. -/
theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) :
    U = Q ∨ (∃ d : Ambient, MulAut.conj d • U = LowRow) ∨
      Covered S8Sylow128SelectedRows.rows U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with heq | heq | ⟨i, d, hd⟩
  · left
    have hsame : MulAut.conj c • U = MulAut.conj c • Q := heq.trans hc.symm
    have h := congrArg (fun W : Subgroup Ambient => MulAut.conj c⁻¹ • W) hsame
    simpa only [map_inv, inv_smul_smul] using h
  · exact Or.inr (Or.inl ⟨c, heq⟩)
  · right; right
    refine ⟨i, d * c, ?_⟩
    rw [map_mul, mul_smul, hd]

theorem seed_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 6) (by
    change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T31.generators)) = 64
    exact BinaryMenuCayley8T31.exact_card)

/-- Exact fixed-catalogue point coverage, including the actual192-row
point binding from the selected pilot. -/
theorem canonical_complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) (hnot : ¬ IsPGroup 2 U) :
    ∃ j : Fin 24, ∃ d : Ambient,
      MulAut.conj d • U = Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.canonical j := by
  rcases complete_of_conjugate U Q hQU c hc with heq | ⟨d, hd⟩ | hlarge
  · have hp : IsPGroup 2 U := by
      rw [heq]
      exact S8CanonicalNonbinaryTransport.isPGroup_of_conjugate Q H c hc seed_isPGroup
    exact False.elim (hnot hp)
  · refine ⟨12, S8Seed31LowRowPilot.conjugator * d, ?_⟩
    rw [map_mul, mul_smul, hd]
    exact S8Seed31LowRowPilot.canonical_conjugated
  · exact S8CanonicalNonbinaryTransport.of_large_covered U hnot hlarge

end SymmetricSubgroupAsymptotics.S8Seed31OvergroupCoverage
end
