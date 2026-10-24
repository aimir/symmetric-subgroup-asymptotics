import SymmetricSubgroupAsymptotics.BinaryProjectiveLinearClassBound
import SymmetricSubgroupAsymptotics.PrimitiveSocleTypeAClassEquationCapacity

/-! The same actual cyclic-polynomial cover pays both remaining binary
type-A component capacities. The literal raw socle, model equivalence,
subnormal subgroup and both original primitive degree forms are retained. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_typeA_binary_cyclic
    (D : NonaffineData G X) (r : ℕ) (hr : r = 3 ∨ r = 5)
    (q : CFSG.PrimePower) (hq : q.order = 2) (e : D.Simple ≃* CFSG.Models.A r q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.A r q) := e.symm.isSimpleGroup
  letI : Fintype q.Field := Fintype.ofFinite q.Field
  have hK : Fintype.card q.Field = 2 := by
    rw [← Nat.card_eq_fintype_card, q.card_field, hq]
  have he : q.exponent = 1 :=
    (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2)
      q.exponent_pos.ne' (by decide : (1 : ℕ) ≠ 0)
      (show q.prime^q.exponent = 2^1 from hq)).2
  have hrlo : 2 ≤ r := by omega
  have hc : Nat.card (ConjClasses (CFSG.Models.A r q)) ≤
      (BinaryWeightedMultisetCodes.codes (r+1)).card := by
    simpa only [Fintype.card_fin] using
      BinaryProjectiveLinearClassBound.projective_class_card_le_codes (I := Fin (r+1)) hK
  have ho : Nat.card (Outer (CFSG.Models.A r q)) ≤ 2 := by
    simpa [hq, he] using
      CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd r hrlo q
  have hi : ∀ K : Subgroup (CFSG.Models.A r q), K ≠ ⊤ → 2^r ≤ K.index := by
    intro K hK
    simpa only [hq] using
      CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index r hrlo q K hK
  have hb : 3 ≤ 2^r := (by decide : 3 ≤ 2^2).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) hrlo)
  have hbudget : ((BinaryWeightedMultisetCodes.codes (r+1)).card * 2)^3 ≤ 5^(2^r-1) := by
    rcases hr with rfl | rfl
    · rw [show 3+1=4 from rfl, BinaryWeightedMultisetCodes.card_codes_four]
      decide
    · rw [show 5+1=6 from rfl, BinaryWeightedMultisetCodes.card_codes_six]
      decide
  refine D.subnormal_class_cube_le_of_model_capacity (CFSG.Models.A r q) e
    (2^r) hb hi ((Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3).trans hbudget) ?_ H hH
  obtain ⟨ell, hell⟩ := exists_leastProperIndex (CFSG.Models.A r q)
  obtain ⟨K, hK, hKe⟩ := hell.1
  exact (Nat.pow_le_pow_left ((hi K hK).trans_eq hKe) 2).trans
    (CFSGTypeALeastIndexSquare.typeA_leastProperIndex_square_lt_card r hrlo q ell hell).le

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
