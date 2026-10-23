import SymmetricSubgroupAsymptotics.PrimitiveSocleBoundedComponentClassBound
import SymmetricSubgroupAsymptotics.CFSGTwistedE6OriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! The original twisted-E6 component pays the common large primitive
class-count budget. Both raw socle degree forms and every subgroup are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGTwistedE6OriginalOrderUpper CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.twistedE6_simple_order_outer_budget
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedE6 q) (K : Subgroup D.Simple) (hK : K ≠ ⊤) :
    Nat.card D.Simple * Nat.card (Outer D.Simple) ≤ K.index ^ 66 := by
  letI : IsSimpleGroup (CFSG.Models.TwistedE6 q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TwistedE6 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have hproper : K.map e.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hK
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  have hi := CFSGTwistedE6GeckPermutationDegree.order_square_le_proper_index
    q (K.map e.toMonoidHom) hproper
  have hindex : (K.map e.toMonoidHom).index = K.index := K.index_map_equiv e
  rw [hindex] at hi
  have hq : 1 ≤ q.order := by
    change 1 ≤ q.prime ^ q.exponent
    exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ q.prime_isPrime.ne_zero)
  rw [Nat.card_congr e.toEquiv, outer_card_congr e]
  exact (original_order_mul_outer_le q hn).trans
    ((Nat.pow_le_pow_right hq (by decide : 122 ≤ 2 * 66)).trans
      ((pow_mul q.order 2 66).trans_le (Nat.pow_le_pow_left hi 66)))

theorem NonaffineData.subgroup_class_cube_le_of_twistedE6
    (D : NonaffineData G X) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedE6 q)
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H) ^ 3 ≤ 5 ^ (Nat.card X - 1) := by
  rcases D.indexForm with ⟨K, hK, hdegree⟩ | ⟨a, hka, hdegree⟩
  · exact D.subgroup_class_cube_le_of_bounded_component K hK hdegree
      (D.twistedE6_simple_order_outer_budget q e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
