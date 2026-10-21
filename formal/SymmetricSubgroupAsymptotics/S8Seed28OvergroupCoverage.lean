import SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapeCoverage
import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionEdgeProperty
import SymmetricSubgroupAsymptotics.S8Sylow128OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed28LowRowPilot
import SymmetricSubgroupAsymptotics.S8Seed28Root1Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root2Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root3Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root4Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root5Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root6Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root7Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root8Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root9Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root10Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root11Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root12Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root13Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root14Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root15Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root16Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root18Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root19Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root20Contains128
import SymmetricSubgroupAsymptotics.S8Seed28Root22Contains128

/-! Actual overgroups of original8T28. Its two low root adjunctions are
the same literal subgroup, fixed by every selected forest conjugator.
All other nontrivial roots contain an actual conjugate of original8T35.
The two low rows are nested, so their four joins need no finite table.
No classification statement or numerical group order is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed28OvergroupCoverage
open S8Seed28LeftCosets FiniteSubgroupAdjunctionCoverage

abbrev LargerSeed : Subgroup Ambient := S8Sylow128LeftCosets.H
abbrev LowRow : Subgroup Ambient := S8Seed28LowRowPilot.lowRow

def lowRows : Fin 2 → Subgroup Ambient := ![H, LowRow]

def LowOrLarger (W : Subgroup Ambient) : Prop :=
  (∃ i : Fin 2, W = lowRows i) ∨
    ∃ c : Ambient, MulAut.conj c • LargerSeed ≤ W

theorem lowRows_contain (i : Fin 2) : H ≤ lowRows i := by
  fin_cases i
  · exact le_rfl
  · exact S8Seed28LowRowPilot.seed_le_low

theorem edge_fixes_low (j : Fin 4) (i : Fin 2) :
    MulAut.conj (S8Seed28NormalizerRoots.edgeConjugator j) • lowRows i = lowRows i := by
  fin_cases j
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · fin_cases i
    · exact S8Seed28NormalizerRoots.normalizes_seed
    · exact S8Seed28LowRowPilot.normalizes_low

theorem edge_property (j : Fin 4) (W : Subgroup Ambient) (hW : LowOrLarger W) :
    LowOrLarger (MulAut.conj (S8Seed28NormalizerRoots.edgeConjugator j) • W) := by
  rcases hW with ⟨i, rfl⟩ | ⟨d, hd⟩
  · exact Or.inl ⟨i, edge_fixes_low j i⟩
  · right
    let c := S8Seed28NormalizerRoots.edgeConjugator j
    refine ⟨c * d, ?_⟩
    have hmap : MulAut.conj c • (MulAut.conj d • LargerSeed) ≤
        MulAut.conj c • W := by
      change (MulAut.conj d • LargerSeed).map (MulAut.conj c).toMonoidHom ≤
        W.map (MulAut.conj c).toMonoidHom
      exact Subgroup.map_mono hd
    simpa only [map_mul, mul_smul] using hmap

theorem root_property (k : Fin 23) : LowOrLarger
    (H ⊔ Subgroup.closure {representatives (S8Seed28NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact Or.inl ⟨0, S8Seed28NormalizerRoots.root_zero_eq_seed⟩
  · exact Or.inr ⟨S8Seed28Root1Contains128.conjugator, S8Seed28Root1Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root2Contains128.conjugator, S8Seed28Root2Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root3Contains128.conjugator, S8Seed28Root3Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root4Contains128.conjugator, S8Seed28Root4Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root5Contains128.conjugator, S8Seed28Root5Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root6Contains128.conjugator, S8Seed28Root6Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root7Contains128.conjugator, S8Seed28Root7Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root8Contains128.conjugator, S8Seed28Root8Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root9Contains128.conjugator, S8Seed28Root9Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root10Contains128.conjugator, S8Seed28Root10Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root11Contains128.conjugator, S8Seed28Root11Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root12Contains128.conjugator, S8Seed28Root12Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root13Contains128.conjugator, S8Seed28Root13Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root14Contains128.conjugator, S8Seed28Root14Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root15Contains128.conjugator, S8Seed28Root15Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root16Contains128.conjugator, S8Seed28Root16Contains128.contains_seed⟩
  · exact Or.inl ⟨1, S8Seed28LowRowPilot.low_eq_adjoin.symm⟩
  · exact Or.inr ⟨S8Seed28Root18Contains128.conjugator, S8Seed28Root18Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root19Contains128.conjugator, S8Seed28Root19Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed28Root20Contains128.conjugator, S8Seed28Root20Contains128.contains_seed⟩
  · exact Or.inl ⟨1, S8Seed28LowRowPilot.other_eq_low⟩
  · exact Or.inr ⟨S8Seed28Root22Contains128.conjugator, S8Seed28Root22Contains128.contains_seed⟩

theorem adjoin_property (g : Ambient) : LowOrLarger (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed28LeftCosets.certificate.covers
    SymmetricEightTwoGenerators.generators_full g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (representatives i) hi
  have hp := S8Seed28NormalizerRoots.reduction.edge_property_representative
    LowOrLarger (by
      intro a ha W hW
      change LowOrLarger (MulAut.conj
        (S8Seed28NormalizerRoots.edgeConjugator (S8Seed28NormalizerRoots.letters a)) • W)
      exact edge_property _ W hW) root_property i
  rw [← he] at hp
  exact hp

theorem join_property (i j : Fin 2) : LowOrLarger (lowRows i ⊔ lowRows j) := by
  fin_cases i <;> fin_cases j
  · exact Or.inl ⟨0, sup_idem _⟩
  · exact Or.inl ⟨1, sup_eq_right.mpr S8Seed28LowRowPilot.seed_le_low⟩
  · exact Or.inl ⟨1, sup_eq_left.mpr S8Seed28LowRowPilot.seed_le_low⟩
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

end SymmetricSubgroupAsymptotics.S8Seed28OvergroupCoverage
end
