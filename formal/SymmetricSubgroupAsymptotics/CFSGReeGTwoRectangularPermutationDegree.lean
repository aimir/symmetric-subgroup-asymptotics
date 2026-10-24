import SymmetricSubgroupAsymptotics.CFSGReeGTwoSubgroupCoordinateLayers
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPermutationDegree
import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCentralQuotient

/-! The same literal positive Ree group acts on the original coset space.
A moved central element forces a centre-proper stabilizer. Its three
actual additive layers give degree at least three times the field order,
without any extra torus-invariance or scalar-surjectivity premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoRectangularPermutationDegree

open CFSGReeGTwoFieldParameters CFSGReeGTwoFixedModelEquivalence
open CFSGReeGTwoOriginalPositiveSubgroup CFSGReeGTwoPositiveCentre
open CFSGReeGTwoSubgroupCoordinateLayers CFSGReeGTwoPositiveCentralQuotient
open CFSGReeGTwoDerivedCenter CFSGReeGTwoFixedCardinalitySylow
open PrimitiveSocleRawStructure
attribute [local instance] fixedModel_finite

theorem degree_le_of_central_motion (m : ℕ) {X : Type*} [Finite X]
    [MulAction (fixedPositiveGroup m) X] (x : X) (c : Multiplicative (Field m))
    (hc : centralHom m c • x ≠ x) : 3 * Nat.card (Field m) ≤ Nat.card X := by
  letI : Finite (fixedPositiveGroup m) :=
    Finite.of_equiv (Fin 3 → Field m) (fixedPositiveEquiv m)
  have hL : ¬ (centralHom m).range ≤ MulAction.stabilizer (fixedPositiveGroup m) x := by
    intro hh
    exact hc (hh ⟨c, rfl⟩)
  calc
    3 * Nat.card (Field m) ≤ (MulAction.stabilizer (fixedPositiveGroup m) x).index :=
      three_field_card_le_index m _ hL
    _ = (MulAction.orbit (fixedPositiveGroup m) x).ncard := MulAction.index_stabilizer _ _
    _ ≤ Nat.card X := Set.ncard_le_card _

theorem three_field_card_le_proper_index (m : ℕ) (hm : 1 ≤ m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] (H : Subgroup (CFSG.Models.ReeG2 m))
    (hH : H ≠ ⊤) : 3 * 3 ^ (2 * m + 1) ≤ H.index := by
  letI : Finite (CFSG.Models.ReeG2 m) :=
    Finite.of_equiv (commutator (originalModelFixed m)) (originalReeEquivDerived m hm).symm.toEquiv
  have hz : centralHom m (Multiplicative.ofAdd (1 : Field m)) ≠ 1 := by
    intro he
    have hh := centralHom_injective m
      (he.trans (map_one (centralHom m)).symm)
    exact (one_ne_zero : (1 : Field m) ≠ 0) (congrArg Multiplicative.toAdd hh)
  have hzo : reePositiveHom m hm (centralHom m (Multiplicative.ofAdd (1 : Field m))) ≠ 1 := by
    intro he
    exact hz (reePositiveHom_injective m hm
      (he.trans (map_one (reePositiveHom m hm)).symm))
  obtain ⟨x, hx⟩ := CFSGConjugateSubgroupDegree.exists_moved_coset_of_ne_one H hH _ hzo
  letI : MulAction (fixedPositiveGroup m) (CFSG.Models.ReeG2 m ⧸ H) :=
    MulAction.compHom _ (reePositiveHom m hm)
  have hdeg : 3 * Nat.card (Field m) ≤ Nat.card (CFSG.Models.ReeG2 m ⧸ H) :=
    degree_le_of_central_motion m x (Multiplicative.ofAdd 1) hx
  simpa only [field_card] using hdeg

theorem three_field_card_le_leastProperIndex (m : ℕ) (hm : 1 ≤ m)
    [IsSimpleGroup (CFSG.Models.ReeG2 m)] (ell : ℕ)
    (hell : LeastProperIndex (CFSG.Models.ReeG2 m) ell) :
    3 * 3 ^ (2 * m + 1) ≤ ell := by
  obtain ⟨H, hH, he⟩ := hell.1
  rw [← he]
  exact three_field_card_le_proper_index m hm H hH

end SymmetricSubgroupAsymptotics.CFSGReeGTwoRectangularPermutationDegree
