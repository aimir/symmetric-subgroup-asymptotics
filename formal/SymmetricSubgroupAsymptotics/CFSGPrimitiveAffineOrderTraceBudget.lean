import SymmetricSubgroupAsymptotics.CFSGChiefPrimeFactorBudget
import SymmetricSubgroupAsymptotics.PrimitiveAffineLinearOrderDivisor
import SymmetricSubgroupAsymptotics.PrimitiveAffineMediumOddSource

/-! Actual complement divisors and order-charge bounds for the SAME chosen
chief trace. No solvability, primitive composition length or model locator
is a premise. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
open CFSGChiefPrimeFactorBudget

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem exists_prime_dimension_complement_divisor (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (x : X) :
    ∃ p d : ℕ, p.Prime ∧ 0<d ∧ Nat.card X=p^d ∧
      Nat.card (P.complement x) ∣ fullLinearOrder p d ∧ fullLinearOrder p d ≠ 0 := by
  obtain ⟨p,d,hp',hd,he,hdiv,hne⟩ := P.exists_prime_dimension_order_divisor hp
  have hG : Nat.card G=Nat.card X*Nat.card (P.complement x) := by
    simpa only [P.card_eq x] using (P.isComplement'_complement x).card_mul.symm
  rw [hG,he] at hdiv
  change p^d*Nat.card (P.complement x) ∣ p^d*fullLinearOrder p d at hdiv
  have hc := (Nat.mul_dvd_mul_iff_left (pow_pos hp'.pos d)).1 hdiv
  have hl : fullLinearOrder p d ≠ 0 := by
    intro hz
    apply hne
    simp only [fullAffineOrder,hz,mul_zero]
  exact ⟨p,d,hp',hd,he,hc,hl⟩

theorem complement_divisor_of_degree_eq (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (x : X) {p d : ℕ}
    (hp' : p.Prime) (hd : 0<d) (he : Nat.card X=p^d) :
    Nat.card (P.complement x) ∣ fullLinearOrder p d ∧ fullLinearOrder p d ≠ 0 := by
  obtain ⟨q,e,hq,hed,heq,hdiv,hne⟩ := P.exists_prime_dimension_complement_divisor hp x
  have hh := prime_pow_positive_injective hq hp' hed hd (heq.symm.trans he)
  rcases hh with ⟨rfl,rfl⟩
  exact ⟨hdiv,hne⟩

theorem complementTrace_abelianLength_le_fullLinearOmega (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (x : X) {p d : ℕ}
    (hp' : p.Prime) (hd : 0<d) (he : Nat.card X=p^d)
    (T : FixedTargetCompositionTrace (P.complement x)) :
    T.envelope.abelianLength ≤ ArithmeticFunction.cardFactors (fullLinearOrder p d) := by
  obtain ⟨hdiv,hne⟩ := P.complement_divisor_of_degree_eq hp x hp' hd he
  rw [T.abelianLength_eq]
  exact (actualChiefSeriesAbelianLength_le_cardFactors T.chief).trans
    (cardFactors_mono hne hdiv)

theorem complementTrace_nonsoluble_saving_le_fullLinearOmega (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (x : X) {p d : ℕ}
    (hp' : p.Prime) (hd : 0<d) (he : Nat.card X=p^d)
    (T : FixedTargetCompositionTrace (P.complement x)) (hn : ¬ IsSolvable (P.complement x)) :
    T.envelope.abelianLength+1 ≤ ArithmeticFunction.cardFactors (fullLinearOrder p d) := by
  obtain ⟨hdiv,hne⟩ := P.complement_divisor_of_degree_eq hp x hp' hd he
  exact (trace_nonsoluble_saving T hn).trans (cardFactors_mono hne hdiv)

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
