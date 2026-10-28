import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound

/-! A proved order/outer cap at any proved proper-index lower bound pays
the literal component-index budget. No conjugacy-class profile, actual
group recognition, or global GM input is required. The original D, K,
socle factor count, quotient and both degree forms remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteSimpleOrderCapClassGap
open PrimitiveSocleRawStructure

theorem index_budget {S : Type} [Group S] (L : ℕ)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → L ≤ K.index)
    (hcap : Nat.card S * Nat.card (Outer S) ≤ L ^ 66)
    (K : Subgroup S) (hK : K ≠ ⊤) :
    Nat.card S * Nat.card (Outer S) ≤ K.index ^ 66 :=
  hcap.trans (Nat.pow_le_pow_left (hindex K hK) 66)

theorem no_index_order_failure {S : Type} [Group S] (L : ℕ)
    (hindex : ∀ K : Subgroup S, K ≠ ⊤ → L ≤ K.index)
    (hcap : Nat.card S * Nat.card (Outer S) ≤ L ^ 66)
    (K : Subgroup S) (hK : K ≠ ⊤)
    (hfail : K.index ^ 66 < Nat.card S * Nat.card (Outer S)) : False :=
  (not_lt_of_ge (index_budget L hindex hcap K hK)) hfail

theorem index_budget_of_five_cap {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hn : ¬IsMulCommutative S)
    (hcap : Nat.card S * Nat.card (Outer S) ≤ 5 ^ 66)
    (K : Subgroup S) (hK : K ≠ ⊤) :
    Nat.card S * Nat.card (Outer S) ≤ K.index ^ 66 :=
  index_budget 5
    (nonabelianSimple_proper_index_five_le
      (fun hc => hn (isMulCommutative_iff.mpr hc))) hcap K hK

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem no_original_failure (D : NonaffineData G X) (L : ℕ)
    (hindex : ∀ K : Subgroup D.Simple, K ≠ ⊤ → L ≤ K.index)
    (hcap : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ L ^ 66)
    (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hfail : K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple)) : False :=
  no_index_order_failure L hindex hcap K hK hfail

/-- Every subgroup is covered, for both original degree forms, from
degree 1024 onward. This is stronger than a subnormal-only conclusion. -/
theorem subgroup_class_cube_le (D : NonaffineData G X) (L : ℕ)
    (hindex : ∀ K : Subgroup D.Simple, K ≠ ⊤ → L ≤ K.index)
    (hcap : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ L ^ 66)
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  rcases D.indexForm with ⟨K, hK, hdegree⟩ | ⟨a, hka, hdegree⟩
  · exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree
      (index_budget L hindex hcap K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

theorem subgroup_class_cube_le_of_five_cap (D : NonaffineData G X)
    (hcap : Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ 5 ^ 66)
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) :=
  subgroup_class_cube_le D 5
    (nonabelianSimple_proper_index_five_le
      (fun hc => D.noncommutative (isMulCommutative_iff.mpr hc))) hcap hn H

end SymmetricSubgroupAsymptotics.FiniteSimpleOrderCapClassGap
