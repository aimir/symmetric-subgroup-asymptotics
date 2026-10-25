import SymmetricSubgroupAsymptotics.TypeACoefficientScaledClassEnvelope
import SymmetricSubgroupAsymptotics.FiniteFieldProjectiveLinearClassBound
import SymmetricSubgroupAsymptotics.BinaryProjectiveLinearClassBound
import SymmetricSubgroupAsymptotics.CFSGTypeAOuterGcdCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeAProperIndexOrderBudget
import Mathlib.Data.Nat.Prime.Int

/-! Coefficient-word class bounds on the SAME original projective SL
model pay all binary ranks from four onward and the three rank-three/four
nonbinary heads. Literal lower-rank obstructions are not asserted away. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeACoefficientScaledClassPacket
open PrimitiveSocleRawStructure CFSGReduction

theorem class_card_le_coefficients (r : ℕ) (q : CFSG.PrimePower) :
    Nat.card (ConjClasses (CFSG.Models.A r q)) ≤
      (q.order-1).gcd (r+1)*((q.order-1)*(2*q.order-1)^r) := by
  simpa only [q.card_field,Fintype.card_fin,Nat.add_sub_cancel] using
    (FiniteFieldProjectiveLinearClassBound.projective_class_card_le_coefficients
      (K := q.Field) (I := Fin (r+1)))

private theorem exponent_eq_one (q : CFSG.PrimePower) (p : ℕ)
    (hp : p.Prime) (hq : q.order=p) : q.exponent=1 :=
  (Nat.Prime.pow_inj' q.prime_isPrime hp q.exponent_pos.ne' (by decide : (1:ℕ)≠0)
    (by simpa only [pow_one] using hq : q.prime^q.exponent=p^1)).2

private theorem exponent_eq_two_of_four (q : CFSG.PrimePower) (hq : q.order=4) :
    q.exponent=2 :=
  (Nat.Prime.pow_inj' q.prime_isPrime (by decide : Nat.Prime 2) q.exponent_pos.ne'
    (by decide : (2:ℕ)≠0) (show q.prime^q.exponent=2^2 from hq)).2

theorem scaled_class_cube_le_proper_index (r : ℕ) (q : CFSG.PrimePower)
    (hwindow : (4 ≤ r ∧ q.order=2) ∨ (r=3 ∧ (q.order=3 ∨ q.order=4)) ∨
      (r=4 ∧ q.order=3))
    [IsSimpleGroup (CFSG.Models.A r q)]
    (H : Subgroup (CFSG.Models.A r q)) (hH : H≠⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.A r q))*
      Nat.card (Outer (CFSG.Models.A r q)))^3 ≤ 3^H.index := by
  have hr : 2 ≤ r := by rcases hwindow with h | h | h <;> omega
  have hi := CFSGTypeAProperIndexOrderBudget.typeA_higher_field_power_le_proper_index r hr q H hH
  have ho := CFSGTypeAOuterGcdCardinality.typeA_higher_outer_card_le_gcd r hr q
  apply le_trans ?_ (Nat.pow_le_pow_right (by decide) hi)
  rcases hwindow with ⟨hr4,hq⟩ | ⟨hr3,hq⟩ | ⟨hr4,hq⟩
  · have hf := exponent_eq_one q 2 (by decide) hq
    have ho' : Nat.card (Outer (CFSG.Models.A r q)) ≤ 2 := by
      simpa only [hq,hf,Nat.reduceSub,Nat.gcd_one_left,one_mul,mul_one] using ho
    rw [hq]
    by_cases hr5 : 5 ≤ r
    · have hclasses : Nat.card (ConjClasses (CFSG.Models.A r q)) ≤ 3^r := by
        simpa only [hq,Nat.reduceSub,Nat.reduceMul,Nat.gcd_one_left,one_mul] using
          class_card_le_coefficients r q
      exact (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left
        ((Nat.mul_le_mul hclasses ho').trans_eq (Nat.mul_comm _ _)) 3)).trans
          (TypeACoefficientScaledClassEnvelope.binary_scaled_cube_le r hr5)
    · have hre : r=4 := by omega
      subst r
      letI : Fintype q.Field := Fintype.ofFinite q.Field
      have hfield : Fintype.card q.Field=2 := by
        rw [←Nat.card_eq_fintype_card,q.card_field,hq]
      have hc := BinaryProjectiveLinearClassBound.projective_class_card_le_codes
        (I := Fin 5) hfield
      have hclasses : Nat.card (ConjClasses (CFSG.Models.A 4 q)) ≤ 42 := by
        simpa only [Fintype.card_fin,TypeACoefficientScaledClassEnvelope.card_codes_five] using hc
      exact (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hclasses ho') 3)).trans
        TypeACoefficientScaledClassEnvelope.binary_rank_four_scaled_cube_le
  · subst r
    have hc := class_card_le_coefficients 3 q
    have hf : (q.order=3 ∧ q.exponent=1) ∨ (q.order=4 ∧ q.exponent=2) := by
      rcases hq with hq | hq
      · exact Or.inl ⟨hq,exponent_eq_one q 3 (by decide) hq⟩
      · exact Or.inr ⟨hq,exponent_eq_two_of_four q hq⟩
    exact (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
      (TypeACoefficientScaledClassEnvelope.coefficient_heads_scaled_cube_le 3 q.order q.exponent
        (by
          rcases hf with h | h
          · exact Or.inl ⟨rfl,h⟩
          · exact Or.inr (Or.inl ⟨rfl,h⟩)))
  · subst r
    have hc := class_card_le_coefficients 4 q
    have hf := exponent_eq_one q 3 (by decide) hq
    exact (Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
      (TypeACoefficientScaledClassEnvelope.coefficient_heads_scaled_cube_le 4 q.order q.exponent
        (Or.inr (Or.inr ⟨rfl,hq,hf⟩)))

end SymmetricSubgroupAsymptotics.CFSGTypeACoefficientScaledClassPacket
