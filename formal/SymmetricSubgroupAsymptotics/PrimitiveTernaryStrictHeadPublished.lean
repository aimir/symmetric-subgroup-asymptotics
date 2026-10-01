import SymmetricSubgroupAsymptotics.PrimitiveRelativeHeadSocle
import SymmetricSubgroupAsymptotics.PrimitiveStrictHeadReceipt
import SymmetricSubgroupAsymptotics.C3HighPrimitiveReduction
import SymmetricSubgroupAsymptotics.TransitiveTernaryStability

/-!
# Primitive ternary strict head from published primitive groups

Holt--Roney-Dougal proves the degree-at-least-34 tail.  Below degree 34,
Roney-Dougal's published classification of primitive permutation groups of
degree below 2500, as represented by the pinned PrimGrp 3.4.4 table, gives an
exact catalogue row and the actual socle quotient order.

The literature correspondence retained here contains only standard primitive
socle structure: the actual socle is minimal normal and self-centralizing,
and its quotient order agrees with the selected row.  Lean proves that the
socle has zero relative ternary head, reduces every normal subgroup to the
socle quotient, checks every 3-adic valuation, and proves the strict
three-twentieths inequality.  No normal-subgroup ranks are imported from the
catalogue.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Exact published bounded primitive correspondence at the level needed by
the structural proof.  The row records only degree, catalogue index and
socle-quotient order. -/
structure PrimitiveStrictHeadSocleMatch
    (L X : Type*) [Group L] [Finite L] [Finite X] where
  row : Fin 253
  degree_eq : (primitiveStrictHeadRow row).degree = Nat.card X
  E : Subgroup L
  [E_normal : E.Normal]
  minimal : ∀ B : Subgroup L, B.Normal → B ≤ E → B = ⊥ ∨ B = E
  selfCentralizing :
    ∀ x : L, (∀ e : E, x * (e : L) = (e : L) * x) → x ∈ E
  quotientOrder_eq :
    Nat.card (L ⧸ E) = (primitiveStrictHeadRow row).quotientOrder

attribute [instance] PrimitiveStrictHeadSocleMatch.E_normal

namespace PrimitiveStrictHeadSocleMatch

variable {L X : Type*} [Group L] [Finite L] [Finite X]
  [MulAction L X] [MulAction.IsPreprimitive L X] [Nontrivial X]
  (M : PrimitiveStrictHeadSocleMatch L X)

include M

/-- Every normal subgroup in a matched bounded primitive action satisfies the
strict ternary estimate.  The proof uses the actual socle and never enumerates
the normal-subgroup lattice. -/
theorem strict
    (h3 : Nat.card X ≠ 3) (h4 : Nat.card X ≠ 4)
    (h18 : Nat.card X ≠ 18)
    (N : Subgroup L) [N.Normal] :
    20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) <
      3 * Nat.card X := by
  have hzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 M.E) = 0 :=
    primeRelativeHead_minimalSelfCentralizing_eq_zero_of_primitive
      3 M.E M.minimal M.selfCentralizing h3
  have hhead :=
    primeRelativeHead_le_quotientFactorization_of_minimalHeadZero
      3 M.E M.minimal M.selfCentralizing hzero N
  have hrow3 : (primitiveStrictHeadRow M.row).degree ≠ 3 := by
    rw [M.degree_eq]
    exact h3
  have hrow4 : (primitiveStrictHeadRow M.row).degree ≠ 4 := by
    rw [M.degree_eq]
    exact h4
  have hrow18 : (primitiveStrictHeadRow M.row).degree ≠ 18 := by
    rw [M.degree_eq]
    exact h18
  have hstrict := primitiveStrictHeadRow_strict M.row hrow3 hrow4 hrow18
  calc
    20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
        20 * (Nat.card (L ⧸ M.E)).factorization 3 :=
      Nat.mul_le_mul_left 20 hhead
    _ = 20 * (primitiveStrictHeadRow M.row).ternaryValuation := by
      rw [M.quotientOrder_eq, primitiveStrictHeadRow_valuation]
    _ < 3 * (primitiveStrictHeadRow M.row).degree := hstrict
    _ = 3 * Nat.card X := by rw [M.degree_eq]

/-- At the exceptional degree eighteen the published primitive rows are
actually stronger than the uniform strict inequality: their socle quotients
have order prime to three, so every normal ternary relative head vanishes. -/
theorem degreeEighteen_eq_zero
    (h18 : Nat.card X = 18)
    (N : Subgroup L) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 := by
  have hthree : Nat.card X ≠ 3 := by omega
  have hzero : Module.finrank (ZMod 3)
      (primeRelativeCharacters 3 M.E) = 0 :=
    primeRelativeHead_minimalSelfCentralizing_eq_zero_of_primitive
      3 M.E M.minimal M.selfCentralizing hthree
  have hhead :=
    primeRelativeHead_le_quotientFactorization_of_minimalHeadZero
      3 M.E M.minimal M.selfCentralizing hzero N
  have hrow18 : (primitiveStrictHeadRow M.row).degree = 18 := by
    rw [M.degree_eq, h18]
  have hval : (primitiveStrictHeadRow M.row).ternaryValuation = 0 :=
    primitiveStrictHeadRow_eighteen_zero M.row hrow18
  have hquot : (Nat.card (L ⧸ M.E)).factorization 3 = 0 := by
    rw [M.quotientOrder_eq, primitiveStrictHeadRow_valuation, hval]
  omega

end PrimitiveStrictHeadSocleMatch

/-- **Published bounded primitive input.**  Every finite faithful primitive
action of degree below 34 is permutation-isomorphic to one of the 253 pinned
PrimGrp rows and its actual socle has the standard minimal,
self-centralizing structure and the row's exact quotient order.

This is the degree-2--33 slice of Roney-Dougal's classification; it contains
no relative-character or normal-subgroup-rank conclusion. -/
def PublishedPrimitiveStrictHeadCatalogueCorrespondence : Prop :=
  ∀ (L X : Type) [Group L] [Finite L] [Finite X] [MulAction L X]
    [FaithfulSMul L X] [MulAction.IsPreprimitive L X] [Nontrivial X],
    Nat.card X < 34 → Nonempty (PrimitiveStrictHeadSocleMatch L X)

/-- The full primitive strict-head theorem from the two published inputs:
Holt--Roney-Dougal for the infinite tail and Roney-Dougal/PrimGrp for the
bounded correspondence.  All relative-character and numerical arguments are
proved in Lean. -/
theorem primitiveTernaryStrictHeadBound_of_published
    (hgen : PrimitiveNormalGeneratorInput)
    (catalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence) :
    PrimitiveTernaryStrictHeadBound := by
  intro G X _ _ _ _ _ _ _ h3 h4 h18 N _
  by_cases hlarge : 34 ≤ Nat.card X
  · exact c1_primitive_relative_tail_faithful hgen hlarge N
  · obtain ⟨M⟩ := catalogue G X (by omega)
    exact M.strict h3 h4 h18 N

/-- Published primitive degree-eighteen actions have zero ternary normal
head.  This is the primitive part of the all-transitive degree-eighteen
theorem; the imprimitive cases are handled separately. -/
theorem primitive_degreeEighteen_ternaryHead_eq_zero
    (catalogue : PublishedPrimitiveStrictHeadCatalogueCorrespondence)
    (G X : Type) [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [MulAction.IsPreprimitive G X] [Nontrivial X]
    (h18 : Nat.card X = 18) (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) = 0 := by
  obtain ⟨M⟩ := catalogue G X (by omega)
  exact M.degreeEighteen_eq_zero h18 N

end SymmetricSubgroupAsymptotics

end
