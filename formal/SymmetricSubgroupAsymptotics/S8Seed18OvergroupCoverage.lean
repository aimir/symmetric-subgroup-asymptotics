import SymmetricSubgroupAsymptotics.S8Seed18AtomRows
import SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapePropertyCoverage
import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionEdgeProperty
import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import SymmetricSubgroupAsymptotics.BinaryEightSeed18Transitivity
import SymmetricSubgroupAsymptotics.S8Seed18Root1BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root2BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root3BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root4BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root5BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root6BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root7BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root8BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root9BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root10BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root11BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root13BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root14BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root15BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root16BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root17BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root18BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root19BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root20BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root21BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root22BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root23BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root24BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root25BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root26BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root27BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root28BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root29BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root30BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root31BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root32BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root33BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root34BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root35BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root36BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root37BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root38BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root39BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root40BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root41BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root42BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root44BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root45BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root46BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root47BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root48BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root49BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root50BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root51BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root53BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root54BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root55BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root56BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root57BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root58BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root59BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root60BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root61BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root62BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root63BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root64BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed18Root65BinaryExtension

/-! Every actual overgroup above original8T18 is one of four low literal
models or contains an actual larger transitive binary subgroup. Two-atom
join closure and selected-edge invariance account for all low cases. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed18OvergroupCoverage
open S8Seed18LeftCosets S8Seed18LowModels S8Seed18AtomRows

abbrev Escape (W : Subgroup Ambient) : Prop :=
  PermutationPrimePowerSeedEscape.ContainsAbove 2 32 W

def LowOrEscape (W : Subgroup Ambient) : Prop :=
  (∃ s : Finset (Fin 2), W = joined s) ∨ Escape W

theorem escape_of_extension (P W : Subgroup Ambient) (hPW : P ≤ W)
    (hP : IsPGroup 2 P) (hHP : H ≤ P) (hcard : 32 < Nat.card P) : Escape W :=
  ⟨P, hPW, hP,
    permutationSubgroupTransitive_mono H P hHP BinaryEightSeed18Transitivity.transitive,
    hcard⟩

theorem root_low_property (k : Fin 66) (i : Fin 4)
    (hk : H ⊔ Subgroup.closure {representatives (S8Seed18NormalizerRoots.roots k)} = rows i) :
    LowOrEscape (H ⊔ Subgroup.closure {representatives (S8Seed18NormalizerRoots.roots k)}) := by
  obtain ⟨s, hs⟩ := model_is_joined i
  exact Or.inl ⟨s, hk.trans hs⟩

theorem root_property (k : Fin 66) : LowOrEscape
    (H ⊔ Subgroup.closure {representatives (S8Seed18NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact root_low_property 0 0 (root_closure 0).symm
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root1BinaryExtension.extended_le_adjoin
      S8Seed18Root1BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root1BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root2BinaryExtension.extended_le_adjoin
      S8Seed18Root2BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root2BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root3BinaryExtension.extended_le_adjoin
      S8Seed18Root3BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root3BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root4BinaryExtension.extended_le_adjoin
      S8Seed18Root4BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root4BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root5BinaryExtension.extended_le_adjoin
      S8Seed18Root5BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root5BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root6BinaryExtension.extended_le_adjoin
      S8Seed18Root6BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root6BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root7BinaryExtension.extended_le_adjoin
      S8Seed18Root7BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root7BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root8BinaryExtension.extended_le_adjoin
      S8Seed18Root8BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root8BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root9BinaryExtension.extended_le_adjoin
      S8Seed18Root9BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root9BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root10BinaryExtension.extended_le_adjoin
      S8Seed18Root10BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root10BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root11BinaryExtension.extended_le_adjoin
      S8Seed18Root11BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root11BinaryExtension.extended_card_gt)
  · exact root_low_property 12 1 (root_closure 12).symm
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root13BinaryExtension.extended_le_adjoin
      S8Seed18Root13BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root13BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root14BinaryExtension.extended_le_adjoin
      S8Seed18Root14BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root14BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root15BinaryExtension.extended_le_adjoin
      S8Seed18Root15BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root15BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root16BinaryExtension.extended_le_adjoin
      S8Seed18Root16BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root16BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root17BinaryExtension.extended_le_adjoin
      S8Seed18Root17BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root17BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root18BinaryExtension.extended_le_adjoin
      S8Seed18Root18BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root18BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root19BinaryExtension.extended_le_adjoin
      S8Seed18Root19BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root19BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root20BinaryExtension.extended_le_adjoin
      S8Seed18Root20BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root20BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root21BinaryExtension.extended_le_adjoin
      S8Seed18Root21BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root21BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root22BinaryExtension.extended_le_adjoin
      S8Seed18Root22BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root22BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root23BinaryExtension.extended_le_adjoin
      S8Seed18Root23BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root23BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root24BinaryExtension.extended_le_adjoin
      S8Seed18Root24BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root24BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root25BinaryExtension.extended_le_adjoin
      S8Seed18Root25BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root25BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root26BinaryExtension.extended_le_adjoin
      S8Seed18Root26BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root26BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root27BinaryExtension.extended_le_adjoin
      S8Seed18Root27BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root27BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root28BinaryExtension.extended_le_adjoin
      S8Seed18Root28BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root28BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root29BinaryExtension.extended_le_adjoin
      S8Seed18Root29BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root29BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root30BinaryExtension.extended_le_adjoin
      S8Seed18Root30BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root30BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root31BinaryExtension.extended_le_adjoin
      S8Seed18Root31BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root31BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root32BinaryExtension.extended_le_adjoin
      S8Seed18Root32BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root32BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root33BinaryExtension.extended_le_adjoin
      S8Seed18Root33BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root33BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root34BinaryExtension.extended_le_adjoin
      S8Seed18Root34BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root34BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root35BinaryExtension.extended_le_adjoin
      S8Seed18Root35BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root35BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root36BinaryExtension.extended_le_adjoin
      S8Seed18Root36BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root36BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root37BinaryExtension.extended_le_adjoin
      S8Seed18Root37BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root37BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root38BinaryExtension.extended_le_adjoin
      S8Seed18Root38BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root38BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root39BinaryExtension.extended_le_adjoin
      S8Seed18Root39BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root39BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root40BinaryExtension.extended_le_adjoin
      S8Seed18Root40BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root40BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root41BinaryExtension.extended_le_adjoin
      S8Seed18Root41BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root41BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root42BinaryExtension.extended_le_adjoin
      S8Seed18Root42BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root42BinaryExtension.extended_card_gt)
  · exact root_low_property 43 2 (root_closure 43).symm
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root44BinaryExtension.extended_le_adjoin
      S8Seed18Root44BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root44BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root45BinaryExtension.extended_le_adjoin
      S8Seed18Root45BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root45BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root46BinaryExtension.extended_le_adjoin
      S8Seed18Root46BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root46BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root47BinaryExtension.extended_le_adjoin
      S8Seed18Root47BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root47BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root48BinaryExtension.extended_le_adjoin
      S8Seed18Root48BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root48BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root49BinaryExtension.extended_le_adjoin
      S8Seed18Root49BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root49BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root50BinaryExtension.extended_le_adjoin
      S8Seed18Root50BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root50BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root51BinaryExtension.extended_le_adjoin
      S8Seed18Root51BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root51BinaryExtension.extended_card_gt)
  · exact root_low_property 52 3 (root_closure 52).symm
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root53BinaryExtension.extended_le_adjoin
      S8Seed18Root53BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root53BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root54BinaryExtension.extended_le_adjoin
      S8Seed18Root54BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root54BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root55BinaryExtension.extended_le_adjoin
      S8Seed18Root55BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root55BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root56BinaryExtension.extended_le_adjoin
      S8Seed18Root56BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root56BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root57BinaryExtension.extended_le_adjoin
      S8Seed18Root57BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root57BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root58BinaryExtension.extended_le_adjoin
      S8Seed18Root58BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root58BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root59BinaryExtension.extended_le_adjoin
      S8Seed18Root59BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root59BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root60BinaryExtension.extended_le_adjoin
      S8Seed18Root60BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root60BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root61BinaryExtension.extended_le_adjoin
      S8Seed18Root61BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root61BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root62BinaryExtension.extended_le_adjoin
      S8Seed18Root62BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root62BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root63BinaryExtension.extended_le_adjoin
      S8Seed18Root63BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root63BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root64BinaryExtension.extended_le_adjoin
      S8Seed18Root64BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root64BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed18Root65BinaryExtension.extended_le_adjoin
      S8Seed18Root65BinaryExtension.extended_isPGroup le_sup_left S8Seed18Root65BinaryExtension.extended_card_gt)

theorem edge_fixes_joined (j : Fin 6) (s : Finset (Fin 2)) :
    MulAut.conj (S8Seed18NormalizerRoots.edgeConjugator j) • joined s = joined s := by
  fin_cases j
  · change MulAut.conj (1 : Ambient) • joined s = joined s
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • joined s = joined s
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • joined s = joined s
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • joined s = joined s
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • joined s = joined s
    simp only [map_one, one_smul]
  · exact conjugates_joined s

theorem edge_property (j : Fin 6) (W : Subgroup Ambient) (hW : LowOrEscape W) :
    LowOrEscape (MulAut.conj (S8Seed18NormalizerRoots.edgeConjugator j) • W) := by
  rcases hW with ⟨s, rfl⟩ | he
  · exact Or.inl ⟨s, edge_fixes_joined j s⟩
  · exact Or.inr (PermutationPrimePowerSeedEscape.conjugate 2 32 _ W he)

theorem adjoin_property (g : Ambient) : LowOrEscape (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed18LeftCosets.certificate.covers
    SymmetricEightTwoGenerators.generators_full g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (representatives i) hi
  have hp := S8Seed18NormalizerRoots.reduction.edge_property_representative
    LowOrEscape (by
      intro a ha W hW
      change LowOrEscape (MulAut.conj
        (S8Seed18NormalizerRoots.edgeConjugator (S8Seed18NormalizerRoots.letters a)) • W)
      exact edge_property _ W hW) root_property i
  rw [← he] at hp
  exact hp

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) :
    (∃ i : Fin 4, U = rows i) ∨ Escape U := by
  have h := FiniteSeedJoinEscapePropertyCoverage.complete_above H Escape
    (fun V W hVW => PermutationPrimePowerSeedEscape.mono 2 32 V W hVW)
    joined (FiniteSeedAtomJoinRows.seed_le H atoms)
    ⟨∅, joined_empty.trans rows_zero⟩ adjoin_property
    (fun s t => Or.inl ⟨s ∪ t, joined_union s t⟩) U hHU
  rcases h with ⟨s, hs⟩ | he
  · obtain ⟨i, hi⟩ := joined_is_model s
    exact Or.inl ⟨i, hs.trans hi⟩
  · exact Or.inr he

/-- The low alternative retains the actual source point conjugator. -/
theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) :
    (∃ i : Fin 4, ∃ d : Ambient, MulAut.conj d • U = rows i) ∨ Escape U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with ⟨i, hi⟩ | he
  · exact Or.inl ⟨i, c, hi⟩
  · right
    have h := PermutationPrimePowerSeedEscape.conjugate 2 32 c⁻¹ _ he
    simpa only [map_inv, inv_smul_smul] using h

theorem seed_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 5) BinaryMenuCayley8T18.exact_card

end SymmetricSubgroupAsymptotics.S8Seed18OvergroupCoverage
end
