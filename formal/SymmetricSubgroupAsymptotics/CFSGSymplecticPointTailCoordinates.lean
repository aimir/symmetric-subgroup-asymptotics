import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup

/-! Fixing the first natural vector, without fixing its partner,
still gives the genuine smaller symplectic tail. Both image vectors
have zero first negative coordinate, so their pairing is exactly the
tail pairing. These statements are literal matrix identities over
every field; no parabolic recognition or characteristic assumption
is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointTailCoordinates
open CFSGSymplecticSerreMatrices CFSGSymplecticStabilizerCoordinates
open CFSGSymplecticTransvectionGeometry
variable (K : Type) [Field K]

def FixesFirstVector (r : ℕ) (A : Mat K (r+1)) : Prop :=
  A *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1

theorem tail_image_negative_zero (r : ℕ) (A : Mat K (r+1))
    (hA : PreservesPairing (r+1) A) (he : FixesFirstVector K r A)
    (v : Index r → K) :
    (A *ᵥ tailExtend r v) (Sum.inr 0) = 0 := by
  have h := hA (tailExtend r v) (Pi.single (Sum.inl 0) 1)
  change A *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 at he
  rw [he, pairing_pos_basis, pairing_pos_basis] at h
  exact (neg_injective h).trans (tailExtend_neg_zero r v)

theorem pairing_eq_tail_negative_zero (r : ℕ) (v w : Index (r+1) → K)
    (hv : v (Sum.inr 0) = 0) (hw : w (Sum.inr 0) = 0) :
    pairing (r+1) v w = pairing r (v ∘ tailIndex r) (w ∘ tailIndex r) := by
  simp [pairing, Fin.sum_univ_succ, hv, hw, tailIndex]

theorem tailMatrix_preserves_pairing_of_fixed_first (r : ℕ) (A : Mat K (r+1))
    (hA : PreservesPairing (r+1) A) (he : FixesFirstVector K r A) :
    PreservesPairing r (tailMatrix r A) := by
  intro v w
  calc
    pairing r ((tailMatrix r A) *ᵥ v) ((tailMatrix r A) *ᵥ w) =
        pairing r ((A *ᵥ tailExtend r v) ∘ tailIndex r)
          ((A *ᵥ tailExtend r w) ∘ tailIndex r) := by
      rw [tailMatrix_mulVec, tailMatrix_mulVec]
    _ = pairing (r+1) (A *ᵥ tailExtend r v) (A *ᵥ tailExtend r w) :=
      (pairing_eq_tail_negative_zero K r _ _
        (tail_image_negative_zero K r A hA he v)
        (tail_image_negative_zero K r A hA he w)).symm
    _ = pairing (r+1) (tailExtend r v) (tailExtend r w) := hA _ _
    _ = pairing r v w := pairing_tailExtend r v w

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointTailCoordinates
