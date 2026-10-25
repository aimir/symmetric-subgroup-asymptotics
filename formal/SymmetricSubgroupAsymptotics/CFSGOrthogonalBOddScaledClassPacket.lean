import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTernaryPuncturedPointIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBBilinearOrderUpper
import SymmetricSubgroupAsymptotics.CFSGConjugacyMinimumIndexBound

/-! Every actual odd-characteristic original B model of rank at least
three has the scaled class-equation packet. The correct bilinear order
exponent2*r^2+3*r+1 is retained. The only exceptional scalar seed uses
the proved actual ternary rank-three punctured proper index81. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddScaledClassPacket
open PrimitiveSocleRawStructure CFSGReduction

private theorem center_eq_bot {S : Type} [Group S] [IsSimpleGroup S]
    (hn : ¬IsMulCommutative S) : Subgroup.center S=⊥ := by
  rcases (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (hn (Subgroup.center_eq_top_iff.mp h)).elim

private theorem three_mul_le_three_pow (n : ℕ) (hn : 1 ≤ n) : 3*n ≤ 3^n := by
  induction n,hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hp : 1 ≤ (3:ℕ)^n := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    nlinarith

private theorem outer_le_field (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    (hodd : q.prime≠2) [IsSimpleGroup (CFSG.Models.B r q)] :
    Nat.card (Outer (CFSG.Models.B r q)) ≤ q.order := by
  have hp : 3 ≤ q.prime := by have := q.prime_isPrime.two_le; omega
  calc
    _ ≤ 3*q.exponent := CFSGOrthogonalBOriginalMatrixBounds.typeB_outer_card_le_three_exponent r hr q
    _ ≤ 3^q.exponent := three_mul_le_three_pow q.exponent (by have := q.exponent_pos; omega)
    _ ≤ q.prime^q.exponent := Nat.pow_le_pow_left hp _
    _ = q.order := rfl

theorem typeB_scaled_class_cube_le_proper_index (r : ℕ) (hr : 3 ≤ r)
    (q : CFSG.PrimePower) (hodd : q.prime≠2)
    [IsSimpleGroup (CFSG.Models.B r q)] [Finite (CFSG.Models.B r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.B r q))
    (K : Subgroup (CFSG.Models.B r q)) (hK : K≠⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.B r q))*Nat.card (Outer (CFSG.Models.B r q)))^3 ≤
      3^K.index := by
  have hp : 3 ≤ q.prime := by have := q.prime_isPrime.two_le; omega
  have hq : 3 ≤ q.order := hp.trans (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have horder := CFSGOrthogonalBBilinearOrderUpper.typeB_order_le_bilinear_power r hr q
  have houter := outer_le_field r hr q hodd
  have hcenter := center_eq_bot hn
  by_cases hwindow : 4 ≤ q.order ∨ 4 ≤ r
  · let b := (q.order^(r-1)-1)*q.order^(r-1)
    have hpow : 9 ≤ q.order^(r-1) := (by decide : 9 ≤ (3:ℕ)^2).trans
      ((Nat.pow_le_pow_left hq 2).trans
        (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega)))
    have hb : 0 < b := Nat.mul_pos (by omega) (by omega)
    have hindex : ∀ J : Subgroup (CFSG.Models.B r q), J≠⊤ → b ≤ J.index :=
      fun J hJ => typeB_point_radical_le_proper_index r hr q hodd J hJ
    have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
      b hb hcenter hindex).trans (Nat.add_le_add_right (Nat.div_le_div_right horder) 1)
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc houter) 3)).trans
      (OrthogonalBOddScaledClassEnvelope.scaled_class_equation_budget q.order r hq hr hwindow)).trans
        (Nat.pow_le_pow_right (by decide) (hindex K hK))
  · have hr3 : r=3 := by omega
    have hq3 : q.order=3 := by omega
    subst r
    have hindex : ∀ J : Subgroup (CFSG.Models.B 3 q), J≠⊤ → 81 ≤ J.index :=
      fun J hJ => typeB_rank_three_three_field_le_proper_index q hq3 J hJ
    have horder3 : Nat.card (CFSG.Models.B 3 q) ≤ 3^28 := by
      simpa only [hq3,Nat.reducePow,Nat.reduceMul,Nat.reduceAdd] using horder
    have houter3 : Nat.card (Outer (CFSG.Models.B 3 q)) ≤ 3 := by
      simpa only [hq3] using houter
    have hc := (CFSGConjugacyMinimumIndexBound.class_card_le_div_add_one
      81 (by decide) hcenter hindex).trans
        (Nat.add_le_add_right (Nat.div_le_div_right horder3) 1)
    exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left (Nat.mul_le_mul hc houter3) 3)).trans
      OrthogonalBOddScaledClassEnvelope.rank_three_three_field_budget).trans
        (Nat.pow_le_pow_right (by decide) (hindex K hK))

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBOddScaledClassPacket
