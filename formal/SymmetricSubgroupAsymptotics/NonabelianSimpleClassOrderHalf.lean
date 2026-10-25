import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
import SymmetricSubgroupAsymptotics.NonabelianSimpleProperIndex

/-! A finite nonabelian simple group's class count is at most half its
order. The same group's proper-index bound and class equation supply
the saving; no parity or classification input is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NonabelianSimpleClassOrderHalf

theorem twice_class_card_le_order {G : Type*} [Group G] [Finite G]
    [IsSimpleGroup G] (hn : ¬IsMulCommutative G) :
    2*Nat.card (ConjClasses G) ≤ Nat.card G := by
  have hz : Subgroup.center G=⊥ := by
    rcases (inferInstance : (Subgroup.center G).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim
  have hi : ∀ K : Subgroup G, K ≠ ⊤ → 5 ≤ K.index :=
    nonabelianSimple_proper_index_five_le
      (fun h => hn (isMulCommutative_iff.mpr h))
  have hc := CFSGConjugacyMinimumIndexBound.class_card_mul_index_le 5 hz hi
  have ho : 5 ≤ Nat.card G := by
    simpa only [Subgroup.index_bot] using hi ⊥ bot_ne_top
  omega

end SymmetricSubgroupAsymptotics.NonabelianSimpleClassOrderHalf
