import SymmetricSubgroupAsymptotics.SymplecticRankTwoBinaryScaledClassEnvelope
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoSharpIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound

/-! The SAME original binary C2 model pays the scaled class packet
over every field of size at least8, using its actual square index,
literal quadratic order bound and existing outer reconstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoScaledTail
open PrimitiveSocleRawStructure CFSGReduction

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hp : q.prime=2)
    (hq : 8 ≤ q.order) [IsSimpleGroup (CFSG.Models.C 2 q)] [Finite (CFSG.Models.C 2 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.C 2 q))
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.C 2 q))*
      Nat.card (Outer (CFSG.Models.C 2 q)))^3 ≤ 3^H.index := by
  have hindex : ∀ K : Subgroup (CFSG.Models.C 2 q), K ≠ ⊤ → q.order^2 ≤ K.index :=
    typeC_rankTwo_binary_field_square_le_proper_index_of_four_le q hp (by omega)
  have hz : Subgroup.center (CFSG.Models.C 2 q)=⊥ := by
    rcases (inferInstance : (Subgroup.center (CFSG.Models.C 2 q)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim
  have horder : Nat.card (CFSG.Models.C 2 q) ≤ q.order^10 :=
    CFSGSymplecticSharpOrderUpper.typeC_order_le_quadratic_power 2 (by decide) q
  have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
    (q.order^2) (pow_pos (by omega : 0 < q.order) 2) hz hindex).trans
      (Nat.add_le_add_right (Nat.div_le_div_right horder) 1)
  have hout : Nat.card (Outer (CFSG.Models.C 2 q)) ≤ 3*q.exponent := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
      typeC_outer_card_le 2 (by decide) q
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have ho : Nat.card (Outer (CFSG.Models.C 2 q)) ≤ q.order^2 :=
    hout.trans ((Nat.mul_le_mul (by omega : 3 ≤ q.order) hf).trans_eq (pow_two q.order).symm)
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
    (SymplecticRankTwoBinaryScaledClassEnvelope.scaled_class_equation_budget q.order hq)).trans
      (Nat.pow_le_pow_right (by decide) (hindex H hH))

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoScaledTail
