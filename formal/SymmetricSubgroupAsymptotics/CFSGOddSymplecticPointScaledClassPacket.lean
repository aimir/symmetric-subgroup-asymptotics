import SymmetricSubgroupAsymptotics.RankThreePointRadicalScaledClassEnvelope
import SymmetricSubgroupAsymptotics.OrthogonalPointRadicalScaledClassEnvelope
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound
import SymmetricSubgroupAsymptotics.CFSGSymplecticSharpComponentOrderCube
import SymmetricSubgroupAsymptotics.CFSGSymplecticOddHigherRankIndex

/-! The actual odd C index dominates a point-radical quantity. Its
proved order and outer bounds therefore feed one
class-equation proof in every rank at least three. No class count for
an arbitrary subgroup is inferred by enlargement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOddSymplecticPointScaledClassPacket
open PrimitiveSocleRawStructure CFSGReduction OrthogonalPointRadicalOrderCubeNumerics

private theorem field_three_le (q : CFSG.PrimePower) (hodd : q.prime ≠ 2) :
    3 ≤ q.order := by
  have hp : 2 ≤ q.prime := q.prime_isPrime.two_le
  exact (show 3 ≤ q.prime by omega).trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)

private theorem center_eq_bot {S : Type} [Group S] [IsSimpleGroup S]
    (hn : ¬IsMulCommutative S) : Subgroup.center S=⊥ := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim

private theorem scaled_of_point_index {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (r q : ℕ) (hr : 3 ≤ r) (hq : 3 ≤ q) (hn : ¬IsMulCommutative S)
    (horder : Nat.card S ≤ q^(2*r^2+r)) (houter : Nat.card (Outer S) ≤ q^3)
    (hi : ∀ K : Subgroup S, K ≠ ⊤ → (q^(r-1)-1)*q^(r-1) ≤ K.index)
    (K : Subgroup S) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses S)*Nat.card (Outer S))^3 ≤ 3^K.index := by
  by_cases hr4 : 4 ≤ r
  · have hb : 0 < minusIndex q r := lt_of_lt_of_le (by decide : 0 < 32)
      (minusIndex_ge_thirtyTwo q r (by omega) hr4 (Or.inl hq))
    have hindex : ∀ J : Subgroup S, J ≠ ⊤ → minusIndex q r ≤ J.index := by
      intro J hJ
      have hp : q^(r-2)-1 ≤ q^(r-1)-1 := Nat.sub_le_sub_right
        (Nat.pow_le_pow_right (by omega : 0 < q) (by omega : r-2 ≤ r-1)) 1
      exact (Nat.mul_le_mul_right _ hp).trans (hi J hJ)
    have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
      (minusIndex q r) hb (center_eq_bot hn) hindex).trans
      (Nat.add_le_add_right (Nat.div_le_div_right horder) 1)
    have ho : Nat.card (Outer S) ≤ q^6 := houter.trans
      (Nat.pow_le_pow_right (by omega : 0 < q) (by decide : 3 ≤ 6))
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc ho) 3)).trans
      (OrthogonalPointRadicalScaledClassEnvelope.scaled_class_equation_budget
        q r (by omega) hr4 (Or.inl hq))).trans
        (Nat.pow_le_pow_right (by decide) (hindex K hK))
  · have hr3 : r=3 := by omega
    subst r
    have hindex : ∀ J : Subgroup S, J ≠ ⊤ → (q^2-1)*q^2 ≤ J.index := hi
    have hq2 : 9 ≤ q^2 := (by decide : 9 ≤ (3:ℕ)^2).trans
      (Nat.pow_le_pow_left hq 2)
    have hb : 0 < (q^2-1)*q^2 := Nat.mul_pos (by omega) (by omega)
    have horder21 : Nat.card S ≤ q^21 := horder
    have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
      ((q^2-1)*q^2) hb (center_eq_bot hn) hindex).trans
      (Nat.add_le_add_right (Nat.div_le_div_right horder21) 1)
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc houter) 3)).trans
      (RankThreePointRadicalScaledClassEnvelope.scaled_class_equation_budget q hq)).trans
        (Nat.pow_le_pow_right (by decide) (hindex K hK))

private theorem three_exponent_le (q : CFSG.PrimePower) (hq : 3 ≤ q.order) :
    3*q.exponent ≤ q.order^3 := by
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hthree : 3 ≤ q.order^2 := (by decide : 3 ≤ (3:ℕ)^2).trans
    (Nat.pow_le_pow_left hq 2)
  exact (Nat.mul_le_mul hthree hf).trans_eq (pow_succ q.order 2).symm

theorem typeC_scaled_class_cube_le_proper_index (r : ℕ) (hr : 3 ≤ r)
    (q : CFSG.PrimePower) (hodd : q.prime ≠ 2)
    [IsSimpleGroup (CFSG.Models.C r q)] [Finite (CFSG.Models.C r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.C r q))
    (K : Subgroup (CFSG.Models.C r q)) (hK : K ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.C r q))*
      Nat.card (Outer (CFSG.Models.C r q)))^3 ≤ 3^K.index := by
  have hq := field_three_le q hodd
  have hTwo : (2 : q.Field) ≠ 0 :=
    CharP.cast_ne_zero_of_ne_of_prime (R := q.Field) (p := q.prime) Nat.prime_two hodd
  have hout : Nat.card (Outer (CFSG.Models.C r q)) ≤ 3*q.exponent := by
    simpa only [CFSGFiniteFieldAutomorphisms.primePower_card_ringAut q] using
      typeC_outer_card_le r (by omega) q
  apply scaled_of_point_index r q.order hr hq hn
    (CFSGSymplecticSharpOrderUpper.typeC_order_le_quadratic_power r (by omega) q)
    (hout.trans (three_exponent_le q hq)) ?_ K hK
  intro J hJ
  calc
    (q.order^(r-1)-1)*q.order^(r-1) ≤ q.order^(r-1)*q.order^(r-1) :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = q.order^(2*r-2) := by
      rw [←pow_add]
      exact congrArg (fun n : ℕ => q.order^n) (by omega)
    _ ≤ q.prime*q.order^(2*r-2) := Nat.le_mul_of_pos_left _ q.prime_isPrime.pos
    _ ≤ J.index := typeC_odd_prime_mul_field_power_le_proper_index r hr q hTwo J hJ

end SymmetricSubgroupAsymptotics.CFSGOddSymplecticPointScaledClassPacket
