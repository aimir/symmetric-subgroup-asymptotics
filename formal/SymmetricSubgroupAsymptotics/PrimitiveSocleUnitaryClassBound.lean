import SymmetricSubgroupAsymptotics.PrimitiveSocleIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGUnitaryProperIndexOuterUpper
import SymmetricSubgroupAsymptotics.CFSGClassificationTransport
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Every subgroup of the ORIGINAL primitive group satisfies the class
cube bound at degree at least1024 when its actual simple socle type is
an admissible original unitary model. The actual proper subgroup is
transported by the classification isomorphism, and the SAME full-socle
quotient embedding supplies the ambient order. No automorphism/order
budget is retained as a callback. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.unitary_simple_order_outer_budget
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (K : Subgroup D.Simple) (hK : K≠⊤) :
    Nat.card D.Simple*Nat.card (Outer D.Simple) ≤ K.index^(4*Nat.log 2 K.index+23) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA r q) := e.symm.isSimpleGroup
  have hn : ¬IsMulCommutative (CFSG.Models.TwistedA r q) :=
    fun h => D.noncommutative ((CFSGReduction.isMulCommutative_congr e).mpr h)
  have hmap : K.map e.toMonoidHom≠⊤ := by
    intro ht
    apply hK
    apply top_unique
    intro x _
    have hx : e x∈K.map e.toMonoidHom := by rw [ht]; trivial
    obtain ⟨y,hy,he⟩ := hx
    exact (e.injective he) ▸ hy
  have hb := CFSGTwistedAUnitaryCoordinates.twistedA_admissible_order_mul_outer_le_proper_index_log_power
    r hr q hsmall hn (K.map e.toMonoidHom) hmap
  have hidx : (K.map e.toMonoidHom).index=K.index := K.index_map_equiv e
  rw [hidx] at hb
  rw [Nat.card_congr e.toEquiv,CFSGReduction.outer_card_congr e]
  exact hb.trans (Nat.pow_le_pow_right (by have := K.one_lt_index_of_ne_top hK; omega)
    (by omega))

theorem NonaffineData.subgroup_class_cube_le_of_unitary
    (D : NonaffineData G X) (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hsmall : r=2 → q.order≠2) (e : D.Simple ≃* CFSG.Models.TwistedA r q)
    (hn : 1024 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  rcases D.indexForm with ⟨K,hK,hdegree⟩ | ⟨a,hka,hdegree⟩
  · exact D.subgroup_class_cube_le_of_index_order_budget K hK hdegree
      (D.unitary_simple_order_outer_budget r hr q hsmall e K hK) hn H
  · exact D.subgroup_class_cube_le_of_power_form a hka hdegree hn H

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
