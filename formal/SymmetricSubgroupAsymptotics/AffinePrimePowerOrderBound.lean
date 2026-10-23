import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.PGroupAutomorphismCardinality

/-! The actual affine-profile order bound uses log in its ORIGINAL
regular subgroup's prime, uniformly for all finite p-groups. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.AffinePrimePowerOrderBound
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem card_le_degree_mul_prime_log_power (x : X) :
    Nat.card G ≤ Nat.card X*(Nat.card X)^Nat.log P.p (Nat.card X) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  have hAut := PGroupAutomorphismCardinality.mulAut_card_le_pow_log P.p P.V P.V_pgroup
  have hc := (P.complement_card_le_mulEquiv x).trans hAut
  calc
    Nat.card G = Nat.card P.V*Nat.card (P.complement x) :=
      (P.isComplement'_complement x).card_mul.symm
    _ ≤ Nat.card P.V*(Nat.card P.V)^Nat.log P.p (Nat.card P.V) :=
      Nat.mul_le_mul_left _ hc
    _ = Nat.card X*(Nat.card X)^Nat.log P.p (Nat.card X) := by rw [P.card_eq x]

end SymmetricSubgroupAsymptotics.AffinePrimePowerOrderBound
