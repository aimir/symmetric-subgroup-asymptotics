import SymmetricSubgroupAsymptotics.ActualCentralC4ActiveRestrictionCount

/-! Structural coordinates on an actual central extension of repeated
natural binary planes. The finite top may be C3 or S3; its selected cubic
acts on every active plane by the same scalar. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

structure ScalarFourCentralC4TopCoordinates
    (Q T : Type) [Group Q] [Group T] (c d : ℕ) where
  top : Q →* T
  top_surjective : Function.Surjective top
  cubic : T
  active : top.ker →* (Fin d → ScalarFour)
  central : ∀ z : active.ker, ∀ g : Q,
    (((z : top.ker) : Q))*g=g*(((z : top.ker) : Q))
  centralCoordinates : active.ker →* (Fin c → Multiplicative (ZMod 4))
  centralCoordinates_injective : Function.Injective centralCoordinates
  cubic_action : ∀ v : Q, top v=cubic → ∀ k : top.ker, ∀ j,
    active (MulAut.conjNormal v k) j=scalarFourTwist 1 (active k j)

namespace ScalarFourCentralC4TopCoordinates
variable {Q T F : Type} [Group Q] [Group T] [Group F] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

/-- Centrality is in the original target, so the cubic fixes the retained
central kernel even for a nonsplit extension. -/
theorem central_fixed (v : Q) (z : D.active.ker) :
    MulAut.conjNormal v (z : D.top.ker)=(z : D.top.ker) := by
  apply Subtype.ext
  change v*(((z : D.top.ker) : Q))*v⁻¹=(((z : D.top.ker) : Q))
  rw [← D.central z v,mul_assoc,mul_inv_cancel,mul_one]

/-- All source restrictions for one actual cubic lift share this bound. -/
theorem restriction_card_le [Finite F] [Finite Q]
    (alpha : F → F) (v : Q) (hv : D.top v=D.cubic) :
    Nat.card (ActualCentralC4ActiveRestrictionCount.Restriction alpha
      (MulAut.conjNormal v : D.top.ker ≃* D.top.ker)) ≤ Nat.card (F →* InvariantC4Scalar)^(max c d) := by
  apply ActualCentralC4ActiveRestrictionCount.restriction_card_le alpha
    (MulAut.conjNormal v) D.active
    (fun z k => Subtype.ext (D.central z (k : Q)))
    (D.central_fixed v)
    (fun k j => D.cubic_action v hv k j)
    D.centralCoordinates D.centralCoordinates_injective
end ScalarFourCentralC4TopCoordinates
end SymmetricSubgroupAsymptotics
