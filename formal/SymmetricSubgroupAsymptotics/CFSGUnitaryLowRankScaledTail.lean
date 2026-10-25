import SymmetricSubgroupAsymptotics.TypeAScaledOrderEnvelope
import SymmetricSubgroupAsymptotics.CFSGUnitaryIsometryOrderUpper
import SymmetricSubgroupAsymptotics.CFSGUnitaryProperIndexOuterUpper

/-! Two field tails for the SAME original low-rank unitary models.
The proved isometry order and actual proper-index bounds suffice; no
bounded-head classification or supplied class capacity is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryLowRankScaledTail
open PrimitiveSocleRawStructure CFSGTwistedAUnitaryCoordinates

theorem scaled_class_cube_le_proper_index (r : ℕ) (q : CFSG.PrimePower)
    (hwindow : (r=2 ∧ 11 ≤ q.order) ∨ (r=3 ∧ 5 ≤ q.order))
    [IsSimpleGroup (CFSG.Models.TwistedA r q)] [Finite (CFSG.Models.TwistedA r q)]
    (hn : ¬IsMulCommutative (CFSG.Models.TwistedA r q))
    (H : Subgroup (CFSG.Models.TwistedA r q)) (hH : H ≠ ⊤) :
    25*(Nat.card (ConjClasses (CFSG.Models.TwistedA r q))*
      Nat.card (Outer (CFSG.Models.TwistedA r q)))^3 ≤ 3^H.index := by
  have hr : 2 ≤ r := by rcases hwindow with h | h <;> omega
  have hsmall : r=2 → q.order≠2 := by rcases hwindow with h | h <;> omega
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  have hf : q.exponent ≤ q.order := q.exponent.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_left q.prime_isPrime.two_le q.exponent)
  have hrpow : 2*(r+1) ≤ q.order^(r+1) := by
    have hh : r+1 ≤ 2^r := Nat.succ_le_of_lt r.lt_two_pow_self
    have he : 2*(r+1) ≤ 2^(r+1) :=
      (Nat.mul_le_mul_left 2 hh).trans_eq (by rw [pow_succ]; ring)
    exact he.trans (Nat.pow_le_pow_left hq _)
  have ho : Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ q.order^(r+2) := by
    calc
      _ ≤ 2*(r+1)*q.exponent :=
        twistedA_admissible_raw_outer_order_le r hr q hsmall hn
      _ ≤ q.order^(r+1)*q.order := Nat.mul_le_mul hrpow hf
      _ = q.order^(r+2) := (pow_succ q.order (r+1)).symm
  have hc : Nat.card (ConjClasses (CFSG.Models.TwistedA r q)) ≤
      q.order^((r+1)*(r+2)) :=
    (Nat.card_le_card_of_surjective ConjClasses.mk ConjClasses.mk_surjective).trans
      (twistedA_admissible_order_le_isometry_power r hr q hsmall)
  have hcomponent : Nat.card (ConjClasses (CFSG.Models.TwistedA r q))*
      Nat.card (Outer (CFSG.Models.TwistedA r q)) ≤ q.order^((r+2)^2) :=
    (Nat.mul_le_mul hc ho).trans_eq (by
      rw [←pow_add]
      exact congrArg (fun n : ℕ => q.order^n) (by ring))
  have hscalar : 25*(q.order^((r+2)^2))^3 ≤ 3^(q.order^r) := by
    rcases hwindow with ⟨rfl,hq11⟩ | ⟨rfl,hq5⟩
    · have hh := QuadraticExponentialPolynomialTail.polynomial_tail 25 48 3 1 11
        (by decide) (by decide) (by decide +kernel) (by decide +kernel) q.order hq11
      have he : (q.order^((2+2)^2))^3=q.order^48 := by
        rw [←pow_mul]
        exact congrArg (fun n : ℕ => q.order^n) (by decide : (2+2)^2*3=48)
      simpa only [he,one_mul] using hh
    · exact TypeAScaledOrderEnvelope.higher_scaled_order_cube_le q.order 3 hq
        (Or.inr (Or.inr (Or.inr ⟨rfl,hq5⟩)))
  exact ((Nat.mul_le_mul_left 25 (Nat.pow_le_pow_left hcomponent 3)).trans hscalar).trans
    (Nat.pow_le_pow_right (by decide)
      (twistedA_admissible_field_power_le_proper_index r hr q hsmall H hH))

end SymmetricSubgroupAsymptotics.CFSGUnitaryLowRankScaledTail
