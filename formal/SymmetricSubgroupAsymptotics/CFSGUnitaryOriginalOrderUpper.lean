import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryProjectiveCover
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankTwoTorus

/-! A direct upper bound for the ORIGINAL unitary simple model. The
proved natural covers are surjective, and their domains inject into
the full matrix space over the quadratic field. No unitary order
formula or identification with an independently named group is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem naturalFixed_card_le_matrix_space (q : CFSG.PrimePower) (r : ℕ) :
    Nat.card (naturalFixed r q) ≤ q.order ^ (2*(r+1)^2) := by
  let encode : naturalFixed r q → Mat (q.Extension 2) r := fun g => g.val.val
  have hi : Function.Injective encode := by
    intro g h he
    apply Subtype.ext
    apply Subtype.ext
    exact Units.ext he
  have hc := Nat.card_le_card_of_injective encode hi
  have hm : Nat.card (Mat (q.Extension 2) r) = q.order ^ (2*(r+1)^2) := by
    change Nat.card (Fin (r+1) → Fin (r+1) → q.Extension 2) = _
    simp only [Nat.card_fun,Nat.card_fin,extension_two_card,←pow_mul]
    congr 1
    ring
  exact hc.trans_eq hm

theorem twistedA_admissible_order_le_matrix_space (r : ℕ) (hr : 2 ≤ r)
    (q : CFSG.PrimePower) (hsmall : r=2 → q.order≠2) :
    Nat.card (CFSG.Models.TwistedA r q) ≤ q.order ^ (2*(r+1)^2) := by
  by_cases htwo : r=2
  · subst r
    have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans
      (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.prime)
    have hq : 3 ≤ q.order := by have := hsmall rfl; omega
    exact (Nat.card_le_card_of_surjective (rankTwoProjectiveCover q hq)
      (rankTwoProjectiveCover_surjective q hq)).trans
        (naturalFixed_card_le_matrix_space q 2)
  · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r=s+3 := ⟨r-3,by omega⟩
    exact (Nat.card_le_card_of_surjective (unitaryProjectiveCover q s)
      (unitaryProjectiveCover_surjective q s)).trans
        (naturalFixed_card_le_matrix_space q (s+3))

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
