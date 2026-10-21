import SymmetricSubgroupAsymptotics.FiniteSeedJoinEscapePropertyCoverage
import SymmetricSubgroupAsymptotics.FiniteNormalizerAdjunctionEdgeProperty
import SymmetricSubgroupAsymptotics.PermutationPrimePowerSeedEscape
import SymmetricSubgroupAsymptotics.BinaryEightSeed22Transitivity
import SymmetricSubgroupAsymptotics.S8Seed22LowRowPilot
import SymmetricSubgroupAsymptotics.S8Seed22Root1BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root2BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root3BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root4BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root5BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root6BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root7BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root8BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root9BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root10BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root11BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root12BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root13BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root14BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root15BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root16BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root17BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root18BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root19BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root20BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root21BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root22BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root23BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root24BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root25BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root26BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root27BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root28BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root29BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root30BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root31BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root32BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root33BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root34BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root35BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root36BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root37BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root38BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root39BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root40BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root41BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root42BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root43BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root44BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root46BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root47BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root48BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root49BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root50BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root51BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root52BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root53BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root54BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root55BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root56BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root57BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root58BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root59BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root60BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root61BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root62BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root63BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root64BinaryExtension
import SymmetricSubgroupAsymptotics.S8Seed22Root65BinaryExtension

/-! Actual nested low-row coverage above original8T22. Every other proper
adjunction contains a word-certified larger binary subgroup, retaining
its actual original-point action. No numerical low-row order is an input. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.S8Seed22OvergroupCoverage
open S8Seed22LeftCosets

abbrev Escape (W : Subgroup Ambient) : Prop :=
  PermutationPrimePowerSeedEscape.ContainsAbove 2 32 W
abbrev LowRow : Subgroup Ambient := S8Seed22LowRowPilot.lowRow

def lowRows : Fin 2 → Subgroup Ambient := ![H, LowRow]

def LowOrEscape (W : Subgroup Ambient) : Prop :=
  (∃ i : Fin 2, W = lowRows i) ∨ Escape W

theorem lowRows_contain (i : Fin 2) : H ≤ lowRows i := by
  fin_cases i
  · exact le_rfl
  · exact S8Seed22LowRowPilot.seed_le_low

theorem escape_of_extension (P W : Subgroup Ambient) (hPW : P ≤ W)
    (hP : IsPGroup 2 P) (hHP : H ≤ P) (hcard : 32 < Nat.card P) : Escape W :=
  ⟨P, hPW, hP,
    permutationSubgroupTransitive_mono H P hHP BinaryEightSeed22Transitivity.transitive,
    hcard⟩

theorem edge_fixes_low (j : Fin 6) (i : Fin 2) :
    MulAut.conj (S8Seed22NormalizerRoots.edgeConjugator j) • lowRows i = lowRows i := by
  fin_cases j
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · change MulAut.conj (1 : Ambient) • lowRows i = lowRows i
    simp only [map_one, one_smul]
  · fin_cases i
    · exact S8Seed22NormalizerRoots.normalizes_seed
    · exact S8Seed22LowRowPilot.normalizes_low

theorem edge_property (j : Fin 6) (W : Subgroup Ambient) (hW : LowOrEscape W) :
    LowOrEscape (MulAut.conj (S8Seed22NormalizerRoots.edgeConjugator j) • W) := by
  rcases hW with ⟨i, rfl⟩ | hescape
  · exact Or.inl ⟨i, edge_fixes_low j i⟩
  · exact Or.inr (PermutationPrimePowerSeedEscape.conjugate 2 32 _ W hescape)

theorem root_property (k : Fin 66) : LowOrEscape
    (H ⊔ Subgroup.closure {representatives (S8Seed22NormalizerRoots.roots k)}) := by
  fin_cases k
  · exact Or.inl ⟨0, S8Seed22NormalizerRoots.root_zero_eq_seed⟩
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root1BinaryExtension.extended_le_adjoin
      S8Seed22Root1BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root1BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root2BinaryExtension.extended_le_adjoin
      S8Seed22Root2BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root2BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root3BinaryExtension.extended_le_adjoin
      S8Seed22Root3BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root3BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root4BinaryExtension.extended_le_adjoin
      S8Seed22Root4BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root4BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root5BinaryExtension.extended_le_adjoin
      S8Seed22Root5BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root5BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root6BinaryExtension.extended_le_adjoin
      S8Seed22Root6BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root6BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root7BinaryExtension.extended_le_adjoin
      S8Seed22Root7BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root7BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root8BinaryExtension.extended_le_adjoin
      S8Seed22Root8BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root8BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root9BinaryExtension.extended_le_adjoin
      S8Seed22Root9BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root9BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root10BinaryExtension.extended_le_adjoin
      S8Seed22Root10BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root10BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root11BinaryExtension.extended_le_adjoin
      S8Seed22Root11BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root11BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root12BinaryExtension.extended_le_adjoin
      S8Seed22Root12BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root12BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root13BinaryExtension.extended_le_adjoin
      S8Seed22Root13BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root13BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root14BinaryExtension.extended_le_adjoin
      S8Seed22Root14BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root14BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root15BinaryExtension.extended_le_adjoin
      S8Seed22Root15BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root15BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root16BinaryExtension.extended_le_adjoin
      S8Seed22Root16BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root16BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root17BinaryExtension.extended_le_adjoin
      S8Seed22Root17BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root17BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root18BinaryExtension.extended_le_adjoin
      S8Seed22Root18BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root18BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root19BinaryExtension.extended_le_adjoin
      S8Seed22Root19BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root19BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root20BinaryExtension.extended_le_adjoin
      S8Seed22Root20BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root20BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root21BinaryExtension.extended_le_adjoin
      S8Seed22Root21BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root21BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root22BinaryExtension.extended_le_adjoin
      S8Seed22Root22BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root22BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root23BinaryExtension.extended_le_adjoin
      S8Seed22Root23BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root23BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root24BinaryExtension.extended_le_adjoin
      S8Seed22Root24BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root24BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root25BinaryExtension.extended_le_adjoin
      S8Seed22Root25BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root25BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root26BinaryExtension.extended_le_adjoin
      S8Seed22Root26BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root26BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root27BinaryExtension.extended_le_adjoin
      S8Seed22Root27BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root27BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root28BinaryExtension.extended_le_adjoin
      S8Seed22Root28BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root28BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root29BinaryExtension.extended_le_adjoin
      S8Seed22Root29BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root29BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root30BinaryExtension.extended_le_adjoin
      S8Seed22Root30BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root30BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root31BinaryExtension.extended_le_adjoin
      S8Seed22Root31BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root31BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root32BinaryExtension.extended_le_adjoin
      S8Seed22Root32BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root32BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root33BinaryExtension.extended_le_adjoin
      S8Seed22Root33BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root33BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root34BinaryExtension.extended_le_adjoin
      S8Seed22Root34BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root34BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root35BinaryExtension.extended_le_adjoin
      S8Seed22Root35BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root35BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root36BinaryExtension.extended_le_adjoin
      S8Seed22Root36BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root36BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root37BinaryExtension.extended_le_adjoin
      S8Seed22Root37BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root37BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root38BinaryExtension.extended_le_adjoin
      S8Seed22Root38BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root38BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root39BinaryExtension.extended_le_adjoin
      S8Seed22Root39BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root39BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root40BinaryExtension.extended_le_adjoin
      S8Seed22Root40BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root40BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root41BinaryExtension.extended_le_adjoin
      S8Seed22Root41BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root41BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root42BinaryExtension.extended_le_adjoin
      S8Seed22Root42BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root42BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root43BinaryExtension.extended_le_adjoin
      S8Seed22Root43BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root43BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root44BinaryExtension.extended_le_adjoin
      S8Seed22Root44BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root44BinaryExtension.extended_card_gt)
  · exact Or.inl ⟨1, S8Seed22LowRowPilot.low_eq_adjoin.symm⟩
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root46BinaryExtension.extended_le_adjoin
      S8Seed22Root46BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root46BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root47BinaryExtension.extended_le_adjoin
      S8Seed22Root47BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root47BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root48BinaryExtension.extended_le_adjoin
      S8Seed22Root48BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root48BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root49BinaryExtension.extended_le_adjoin
      S8Seed22Root49BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root49BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root50BinaryExtension.extended_le_adjoin
      S8Seed22Root50BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root50BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root51BinaryExtension.extended_le_adjoin
      S8Seed22Root51BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root51BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root52BinaryExtension.extended_le_adjoin
      S8Seed22Root52BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root52BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root53BinaryExtension.extended_le_adjoin
      S8Seed22Root53BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root53BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root54BinaryExtension.extended_le_adjoin
      S8Seed22Root54BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root54BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root55BinaryExtension.extended_le_adjoin
      S8Seed22Root55BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root55BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root56BinaryExtension.extended_le_adjoin
      S8Seed22Root56BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root56BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root57BinaryExtension.extended_le_adjoin
      S8Seed22Root57BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root57BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root58BinaryExtension.extended_le_adjoin
      S8Seed22Root58BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root58BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root59BinaryExtension.extended_le_adjoin
      S8Seed22Root59BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root59BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root60BinaryExtension.extended_le_adjoin
      S8Seed22Root60BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root60BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root61BinaryExtension.extended_le_adjoin
      S8Seed22Root61BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root61BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root62BinaryExtension.extended_le_adjoin
      S8Seed22Root62BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root62BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root63BinaryExtension.extended_le_adjoin
      S8Seed22Root63BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root63BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root64BinaryExtension.extended_le_adjoin
      S8Seed22Root64BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root64BinaryExtension.extended_card_gt)
  · exact Or.inr (escape_of_extension _ _ S8Seed22Root65BinaryExtension.extended_le_adjoin
      S8Seed22Root65BinaryExtension.extended_isPGroup le_sup_left S8Seed22Root65BinaryExtension.extended_card_gt)

theorem adjoin_property (g : Ambient) : LowOrEscape (H ⊔ Subgroup.closure {g}) := by
  obtain ⟨i, hi⟩ := S8Seed22LeftCosets.certificate.covers
    SymmetricEightTwoGenerators.generators_full g
  have he := FiniteLeftCosetCover.adjoin_eq_of_same_left_coset
    (H := H) g (representatives i) hi
  have hp := S8Seed22NormalizerRoots.reduction.edge_property_representative
    LowOrEscape (by
      intro a ha W hW
      change LowOrEscape (MulAut.conj
        (S8Seed22NormalizerRoots.edgeConjugator (S8Seed22NormalizerRoots.letters a)) • W)
      exact edge_property _ W hW) root_property i
  rw [← he] at hp
  exact hp

theorem join_property (i j : Fin 2) : LowOrEscape (lowRows i ⊔ lowRows j) := by
  fin_cases i <;> fin_cases j
  · exact Or.inl ⟨0, sup_idem _⟩
  · exact Or.inl ⟨1, sup_eq_right.mpr S8Seed22LowRowPilot.seed_le_low⟩
  · exact Or.inl ⟨1, sup_eq_left.mpr S8Seed22LowRowPilot.seed_le_low⟩
  · exact Or.inl ⟨1, sup_idem _⟩

theorem complete (U : Subgroup Ambient) (hHU : H ≤ U) : LowOrEscape U :=
  FiniteSeedJoinEscapePropertyCoverage.complete_above H Escape
    (fun V W hVW hV => PermutationPrimePowerSeedEscape.mono 2 32 V W hVW hV)
    lowRows lowRows_contain ⟨0, rfl⟩ adjoin_property join_property U hHU

theorem complete_of_conjugate (U Q : Subgroup Ambient) (hQU : Q ≤ U)
    (c : Ambient) (hc : MulAut.conj c • Q = H) :
    (∃ i : Fin 2, ∃ d : Ambient, MulAut.conj d • U = lowRows i) ∨ Escape U := by
  have hHU : H ≤ MulAut.conj c • U := by
    rw [← hc]
    change Q.map (MulAut.conj c).toMonoidHom ≤ U.map (MulAut.conj c).toMonoidHom
    exact Subgroup.map_mono hQU
  rcases complete (MulAut.conj c • U) hHU with ⟨i, hi⟩ | hescape
  · exact Or.inl ⟨i, c, hi⟩
  · right
    have h := PermutationPrimePowerSeedEscape.conjugate 2 32 c⁻¹ _ hescape
    simpa only [map_inv, inv_smul_smul] using h

theorem seed_isPGroup : IsPGroup 2 H :=
  IsPGroup.of_card (n := 5) BinaryMenuCayley8T22.exact_card

end SymmetricSubgroupAsymptotics.S8Seed22OvergroupCoverage
end
