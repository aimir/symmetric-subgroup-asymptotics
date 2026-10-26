import SymmetricSubgroupAsymptotics.PrimitiveAlternatingNaturalDegreeRecognition

/-! Half-factorial order recognizes the literal alternating/symmetric
permutation overgroup on the SAME original coordinates. No abstract
alternating-group marking or relabelled faithful action is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitivePermutationHalfOrderRecognition
open PrimitiveSocleRawStructure

theorem alternating_or_top_of_card_lower
    {X : Type} [Finite X] (P : Subgroup (Equiv.Perm X))
    (hX : 2 ≤ Nat.card X)
    (hcard : (Nat.card X).factorial ≤ 2*Nat.card P) :
    letI := Fintype.ofFinite X
    letI := Classical.decEq X
    P=alternatingGroup X ∨ P=⊤ := by
  letI := Fintype.ofFinite X
  letI := Classical.decEq X
  letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hindex : P.index ≤ 2 := by
    have hmul : P.index*Nat.card P ≤ 2*Nat.card P := by
      simpa only [P.index_mul_card,Nat.card_perm] using hcard
    exact Nat.le_of_mul_le_mul_right hmul (Nat.card_pos (α := P))
  exact AlmostSimpleIndexTwoSubnormalClasses.containing_simple_index_two
    (alternatingGroup X) P alternatingGroup.index_eq_two
    (Equiv.Perm.alternatingGroup_le_of_index_le_two hindex)

theorem alternating_or_top_of_single_factor_half_order
    {X : Type} [Finite X] (P : Subgroup (Equiv.Perm X))
    (D : NonaffineData P X) (hk : D.factorCount=1)
    (hX : 2 ≤ Nat.card X)
    (hcard : (Nat.card X).factorial ≤ 2*Nat.card D.Simple) :
    letI := Fintype.ofFinite X
    letI := Classical.decEq X
    P=alternatingGroup X ∨ P=⊤ := by
  have hsoc : Nat.card (finiteGroupSocle P)=Nat.card D.Simple := by
    rw [Nat.card_congr D.socleEquiv.toEquiv,Nat.card_fun,Nat.card_fin,hk,pow_one]
  have hsub : Nat.card D.Simple ≤ Nat.card P := by
    rw [←hsoc]
    exact Nat.card_le_card_of_injective (finiteGroupSocle P).subtype Subtype.val_injective
  exact alternating_or_top_of_card_lower P hX
    (hcard.trans (Nat.mul_le_mul_left 2 hsub))

end SymmetricSubgroupAsymptotics.PrimitivePermutationHalfOrderRecognition
