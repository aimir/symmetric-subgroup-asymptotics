import SymmetricSubgroupAsymptotics.SymplecticRankTwoScaledClassEnvelope
import SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoPrimeIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound

/-! The original odd C2 model has actual proper index at least p*q^2.
Its proved order q^10, class equation and original outer bound3f≤q
therefore pay the scaled packet for every odd finite field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoScaledClassPacket
open PrimitiveSocleRawStructure CFSGReduction

private theorem three_mul_le_three_pow (f : ℕ) (hf : 1 ≤ f) : 3*f ≤ 3^f := by
  induction f,hf using Nat.le_induction with
  | base => decide
  | succ f hf ih =>
    calc
      3*(f+1) ≤ 3*(3*f) := by omega
      _ ≤ 3*3^f := Nat.mul_le_mul_left 3 ih
      _ = 3^(f+1) := (pow_succ' 3 f).symm

theorem scaled_class_cube_le_proper_index (q : CFSG.PrimePower) (hodd : q.prime ≠ 2)
    [IsSimpleGroup (CFSG.Models.C 2 q)] [Finite (CFSG.Models.C 2 q)]
    (hn : ¬IsMulCommutative (CFSG.Models.C 2 q))
    (H : Subgroup (CFSG.Models.C 2 q)) (hH : H ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.C 2 q))*
      Nat.card (Outer (CFSG.Models.C 2 q)))^3 ≤ 3^H.index := by
  have hp3 : 3 ≤ q.prime := by have h := q.prime_isPrime.two_le; omega
  have hq3 : 3 ≤ q.order := hp3.trans (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hindex : ∀ K : Subgroup (CFSG.Models.C 2 q), K ≠ ⊤ → 3*q.order^2 ≤ K.index := by
    intro K hK
    exact (Nat.mul_le_mul_right _ hp3).trans
      (typeC_rankTwo_prime_mul_field_square_le_proper_index q hodd K hK)
  have hz : Subgroup.center (CFSG.Models.C 2 q)=⊥ := by
    rcases (inferInstance : (Subgroup.center (CFSG.Models.C 2 q)).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim
  have horder : Nat.card (CFSG.Models.C 2 q) ≤ q.order^10 :=
    CFSGSymplecticSharpOrderUpper.typeC_order_le_quadratic_power 2 (by decide) q
  have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
    (3*q.order^2) (Nat.mul_pos (by decide) (pow_pos (by omega : 0 < q.order) 2)) hz hindex).trans
      (Nat.add_le_add_right (Nat.div_le_div_right horder) 1)
  have ho : Nat.card (Outer (CFSG.Models.C 2 q)) ≤ q.order := by
    have houter : Nat.card (Outer (CFSG.Models.C 2 q)) ≤ 3*q.exponent := by
      simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
        typeC_outer_card_le 2 (by decide) q
    exact houter.trans ((three_mul_le_three_pow q.exponent q.exponent_pos).trans
      (Nat.pow_le_pow_left hp3 q.exponent))
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
    (SymplecticRankTwoScaledClassEnvelope.scaled_class_equation_budget q.order hq3)).trans
      (Nat.pow_le_pow_right (by decide) (hindex H hH))

end SymmetricSubgroupAsymptotics.CFSGSymplecticOddRankTwoScaledClassPacket
