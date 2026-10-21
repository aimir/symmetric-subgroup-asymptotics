import SymmetricSubgroupAsymptotics.S8Seed29AtomRows
import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionEdgeProperty
import SymmetricSubgroupAsymptotics.S8Sylow128OvergroupCoverage
import SymmetricSubgroupAsymptotics.S8Seed29Root1Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root2Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root5Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root6Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root7Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root8Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root13Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root14Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root15Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root20Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root21Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root24Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root25Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root26Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root27Contains128
import SymmetricSubgroupAsymptotics.S8Seed29Root31Contains128
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot9
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot11
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot12
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot16
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot18
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot19
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot22
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot23
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot28
import SymmetricSubgroupAsymptotics.S8Seed29LowRoot29

/-! Every actual overgroup of original8T29 is a finite join of three
actual low atoms, or contains an actual point-conjugate of original8T35.
Root bindings and escape inclusions are ordinary-word certificates;
the low-family join closure is the finite-set union identity. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed29OvergroupCoverage
open S8Seed29LeftCosets FiniteSubgroupAdjunctionCoverage

abbrev LargerSeed : Subgroup Ambient := S8Sylow128LeftCosets.H

def LowOrLarger (W : Subgroup Ambient) : Prop :=
  (∃ s : Finset (Fin 3), W = S8Seed29AtomRows.joined s) ∨
    ∃ c : Ambient, MulAut.conj c • LargerSeed ≤ W

theorem model_property (i : Fin 8) {W : Subgroup Ambient}
    (hW : W = S8Seed29LowModels.rows i) : LowOrLarger W := by
  obtain ⟨s, hs⟩ := S8Seed29AtomRows.model_is_joined i
  exact Or.inl ⟨s, hW.trans hs⟩

theorem edge_low (j : Fin 6) (s : Finset (Fin 3)) : ∃ t : Finset (Fin 3),
    MulAut.conj (S8Seed29NormalizerRoots.edgeConjugator j) •
      S8Seed29AtomRows.joined s = S8Seed29AtomRows.joined t := by
  fin_cases j
  · refine ⟨s, ?_⟩
    change MulAut.conj (1 : Ambient) • _ = _
    simp only [map_one, one_smul]
  · refine ⟨s, ?_⟩
    change MulAut.conj (1 : Ambient) • _ = _
    simp only [map_one, one_smul]
  · refine ⟨s, ?_⟩
    change MulAut.conj (1 : Ambient) • _ = _
    simp only [map_one, one_smul]
  · refine ⟨s, ?_⟩
    change MulAut.conj (1 : Ambient) • _ = _
    simp only [map_one, one_smul]
  · refine ⟨s, ?_⟩
    change MulAut.conj (1 : Ambient) • _ = _
    simp only [map_one, one_smul]
  · exact ⟨s.image S8Seed29AtomRows.atomPermutation, S8Seed29AtomRows.conjugates_joined s⟩

theorem edge_property (j : Fin 6) (W : Subgroup Ambient) (hW : LowOrLarger W) :
    LowOrLarger (MulAut.conj (S8Seed29NormalizerRoots.edgeConjugator j) • W) := by
  rcases hW with ⟨s, rfl⟩ | ⟨d, hd⟩
  · exact Or.inl (edge_low j s)
  · right
    let c := S8Seed29NormalizerRoots.edgeConjugator j
    refine ⟨c * d, ?_⟩
    have hmap : MulAut.conj c • (MulAut.conj d • LargerSeed) ≤
        MulAut.conj c • W := by
      change (MulAut.conj d • LargerSeed).map (MulAut.conj c).toMonoidHom ≤
        W.map (MulAut.conj c).toMonoidHom
      exact Subgroup.map_mono hd
    simpa only [map_mul, mul_smul] using hmap

theorem root_property (k : Fin 32) : LowOrLarger
    (H ⊔ Subgroup.closure {representatives (S8Seed29NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact model_property 0 (S8Seed29NormalizerRoots.root_zero_eq_seed.trans S8Seed29LowModels.rows_zero.symm)
  · exact Or.inr ⟨S8Seed29Root1Contains128.conjugator, S8Seed29Root1Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root2Contains128.conjugator, S8Seed29Root2Contains128.contains_seed⟩
  · exact model_property 1 (S8Seed29LowModels.root_closure 3).symm
  · exact model_property 2 (S8Seed29LowModels.root_closure 4).symm
  · exact Or.inr ⟨S8Seed29Root5Contains128.conjugator, S8Seed29Root5Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root6Contains128.conjugator, S8Seed29Root6Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root7Contains128.conjugator, S8Seed29Root7Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root8Contains128.conjugator, S8Seed29Root8Contains128.contains_seed⟩
  · exact model_property 2 S8Seed29LowRoot9.exact_eq
  · exact model_property 3 (S8Seed29LowModels.root_closure 10).symm
  · exact model_property 2 S8Seed29LowRoot11.exact_eq
  · exact model_property 2 S8Seed29LowRoot12.exact_eq
  · exact Or.inr ⟨S8Seed29Root13Contains128.conjugator, S8Seed29Root13Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root14Contains128.conjugator, S8Seed29Root14Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root15Contains128.conjugator, S8Seed29Root15Contains128.contains_seed⟩
  · exact model_property 2 S8Seed29LowRoot16.exact_eq
  · exact model_property 4 (S8Seed29LowModels.root_closure 17).symm
  · exact model_property 2 S8Seed29LowRoot18.exact_eq
  · exact model_property 2 S8Seed29LowRoot19.exact_eq
  · exact Or.inr ⟨S8Seed29Root20Contains128.conjugator, S8Seed29Root20Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root21Contains128.conjugator, S8Seed29Root21Contains128.contains_seed⟩
  · exact model_property 1 S8Seed29LowRoot22.exact_eq
  · exact model_property 1 S8Seed29LowRoot23.exact_eq
  · exact Or.inr ⟨S8Seed29Root24Contains128.conjugator, S8Seed29Root24Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root25Contains128.conjugator, S8Seed29Root25Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root26Contains128.conjugator, S8Seed29Root26Contains128.contains_seed⟩
  · exact Or.inr ⟨S8Seed29Root27Contains128.conjugator, S8Seed29Root27Contains128.contains_seed⟩
  · exact model_property 2 S8Seed29LowRoot28.exact_eq
  · exact model_property 2 S8Seed29LowRoot29.exact_eq
  · exact model_property 5 (S8Seed29LowModels.root_closure 30).symm
  · exact Or.inr ⟨S8Seed29Root31Contains128.conjugator, S8Seed29Root31Contains128.contains_seed⟩

theorem adjoin_property (g : Ambient) : LowOrLarger (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed29LeftCosets.certificate.covers
    SymmetricEightTwoGenerators.generators_full g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset (H := H) g (representatives i) hi
  have hp := S8Seed29NormalizerRoots.reduction.edge_property_representative LowOrLarger (by
    intro a ha W hW
    change LowOrLarger (MulAut.conj
      (S8Seed29NormalizerRoots.edgeConjugator (S8Seed29NormalizerRoots.letters a)) • W)
    exact edge_property _ W hW) root_property i
  rw [← he] at hp
  exact hp

theorem low_or_contains (U : Subgroup Ambient) (hHU : H ≤ U) : LowOrLarger U :=
  complete_above_of_seed_joins_or_larger H LargerSeed S8Seed29AtomRows.joined
    (fun s => FiniteSeedAtomJoinRows.seed_le H S8Seed29AtomRows.atoms s)
    ⟨∅, S8Seed29AtomRows.joined_empty.trans S8Seed29LowModels.rows_zero⟩
    adjoin_property (fun s t => Or.inl ⟨s ∪ t, S8Seed29AtomRows.joined_union s t⟩) U hHU

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) :
    (∃ i : Fin 8, U = S8Seed29LowModels.rows i) ∨ Covered S8Sylow128SelectedRows.rows U := by
  rcases low_or_contains U hHU with ⟨s, hs⟩ | ⟨c, hc⟩
  · obtain ⟨i, hi⟩ := S8Seed29AtomRows.joined_is_model s
    exact Or.inl ⟨i, hs.trans hi⟩
  · right
    have hmap : MulAut.conj c⁻¹ • (MulAut.conj c • LargerSeed) ≤ MulAut.conj c⁻¹ • U := by
      change (MulAut.conj c • LargerSeed).map (MulAut.conj c⁻¹).toMonoidHom ≤
        U.map (MulAut.conj c⁻¹).toMonoidHom
      exact Subgroup.map_mono hc
    have hlarge : LargerSeed ≤ MulAut.conj c⁻¹ • U := by
      simpa only [map_inv, inv_smul_smul] using hmap
    obtain ⟨i, d, hd⟩ := S8Sylow128OvergroupCoverage.complete _ hlarge
    refine ⟨i, d * c⁻¹, ?_⟩
    rw [map_mul, mul_smul, hd]

/-- Actual point charts remain ambient conjugators in every branch. -/
theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) :
    (∃ i : Fin 8, ∃ d : Ambient, MulAut.conj d • U = S8Seed29LowModels.rows i) ∨
      Covered S8Sylow128SelectedRows.rows U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with ⟨i, hi⟩ | ⟨i, d, hd⟩
  · exact Or.inl ⟨i, c, hi⟩
  · right
    refine ⟨i, d * c, ?_⟩
    rw [map_mul, mul_smul, hd]

end SymmetricSubgroupAsymptotics.S8Seed29OvergroupCoverage
end
