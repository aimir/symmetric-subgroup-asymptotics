import SymmetricSubgroupAsymptotics.FinitePermutationConjugacyCover
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T31

/-! A selected original class-count certificate using the generic pointwise
verifier. This bound alone does not assert completeness of an action registry. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.BinaryConjugacyClass8T31

theorem class_card_le_twenty_five :
    Nat.card (ConjClasses (Subgroup.closure (Set.range BinaryMenuCayley8T31.generators))) ≤
      25 :=
  (BinaryMenuCayley8T31.certificate.permutation_conjClasses_card_le
    BinaryConjugacyData8T31.representative BinaryConjugacyData8T31.label
    BinaryConjugacyData8T31.conjugator BinaryConjugacyData8T31.conjugates_pointwise).trans
      BinaryConjugacyData8T31.representativeCount_le_twenty_five

end SymmetricSubgroupAsymptotics.BinaryConjugacyClass8T31
