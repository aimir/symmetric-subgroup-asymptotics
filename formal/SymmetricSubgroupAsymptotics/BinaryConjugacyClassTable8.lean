import SymmetricSubgroupAsymptotics.BinaryActionRegistry8
import SymmetricSubgroupAsymptotics.FinitePermutationConjugacyCover
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T15
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T16
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T17
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T18
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T19
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T20
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T21
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T22
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T26
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T27
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T28
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T29
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T30
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T31
import SymmetricSubgroupAsymptotics.GeneratedPrunedActions.ConjugacyCover8T35

/-! Class bounds on the 26 literal degree-eight action representatives.
The first eleven use their exact certified orders, at most sixteen. Each
remaining action uses a sparse conjugacy cover with conjugators in that same
original group. This table alone makes no completeness assertion.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryConjugacyClassTable8

private theorem class_card_le_of_order_eq
    {G : Type*} [Group G] [Finite G] {n : ℕ}
    (horder : Nat.card G = n) (hn : n ≤ 25) :
    Nat.card (ConjClasses G) ≤ 25 := by
  have h := Nat.card_le_card_of_surjective (@ConjClasses.mk G _) ConjClasses.mk_surjective
  rw [horder] at h
  exact h.trans hn

/-- Each existing registry position is bounded using its literal source,
not a catalogue class count or a replacement isomorphic action. -/
theorem action_class_card_le (i : Fin 26) :
    Nat.card (ConjClasses (BinaryActionRegistry8.actions i)) ≤ 25 := by
  fin_cases i
  · exact class_card_le_of_order_eq BinaryMenuCayley8T1.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T2.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T3.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T4.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T5.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T6.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T7.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T8.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T9.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T10.exact_card (by decide)
  · exact class_card_le_of_order_eq BinaryMenuCayley8T11.exact_card (by decide)
  · exact (BinaryMenuCayley8T15.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T15.representative BinaryConjugacyData8T15.label
      BinaryConjugacyData8T15.conjugator BinaryConjugacyData8T15.conjugates_pointwise).trans
        BinaryConjugacyData8T15.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T16.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T16.representative BinaryConjugacyData8T16.label
      BinaryConjugacyData8T16.conjugator BinaryConjugacyData8T16.conjugates_pointwise).trans
        BinaryConjugacyData8T16.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T17.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T17.representative BinaryConjugacyData8T17.label
      BinaryConjugacyData8T17.conjugator BinaryConjugacyData8T17.conjugates_pointwise).trans
        BinaryConjugacyData8T17.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T18.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T18.representative BinaryConjugacyData8T18.label
      BinaryConjugacyData8T18.conjugator BinaryConjugacyData8T18.conjugates_pointwise).trans
        BinaryConjugacyData8T18.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T19.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T19.representative BinaryConjugacyData8T19.label
      BinaryConjugacyData8T19.conjugator BinaryConjugacyData8T19.conjugates_pointwise).trans
        BinaryConjugacyData8T19.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T20.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T20.representative BinaryConjugacyData8T20.label
      BinaryConjugacyData8T20.conjugator BinaryConjugacyData8T20.conjugates_pointwise).trans
        BinaryConjugacyData8T20.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T21.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T21.representative BinaryConjugacyData8T21.label
      BinaryConjugacyData8T21.conjugator BinaryConjugacyData8T21.conjugates_pointwise).trans
        BinaryConjugacyData8T21.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T22.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T22.representative BinaryConjugacyData8T22.label
      BinaryConjugacyData8T22.conjugator BinaryConjugacyData8T22.conjugates_pointwise).trans
        BinaryConjugacyData8T22.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T26.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T26.representative BinaryConjugacyData8T26.label
      BinaryConjugacyData8T26.conjugator BinaryConjugacyData8T26.conjugates_pointwise).trans
        BinaryConjugacyData8T26.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T27.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T27.representative BinaryConjugacyData8T27.label
      BinaryConjugacyData8T27.conjugator BinaryConjugacyData8T27.conjugates_pointwise).trans
        BinaryConjugacyData8T27.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T28.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T28.representative BinaryConjugacyData8T28.label
      BinaryConjugacyData8T28.conjugator BinaryConjugacyData8T28.conjugates_pointwise).trans
        BinaryConjugacyData8T28.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T29.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T29.representative BinaryConjugacyData8T29.label
      BinaryConjugacyData8T29.conjugator BinaryConjugacyData8T29.conjugates_pointwise).trans
        BinaryConjugacyData8T29.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T30.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T30.representative BinaryConjugacyData8T30.label
      BinaryConjugacyData8T30.conjugator BinaryConjugacyData8T30.conjugates_pointwise).trans
        BinaryConjugacyData8T30.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T31.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T31.representative BinaryConjugacyData8T31.label
      BinaryConjugacyData8T31.conjugator BinaryConjugacyData8T31.conjugates_pointwise).trans
        BinaryConjugacyData8T31.representativeCount_le_twenty_five
  · exact (BinaryMenuCayley8T35.certificate.permutation_conjClasses_card_le
      BinaryConjugacyData8T35.representative BinaryConjugacyData8T35.label
      BinaryConjugacyData8T35.conjugator BinaryConjugacyData8T35.conjugates_pointwise).trans
        BinaryConjugacyData8T35.representativeCount_le_twenty_five

end SymmetricSubgroupAsymptotics.BinaryConjugacyClassTable8

end
