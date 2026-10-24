import SymmetricSubgroupAsymptotics.CFSGSymplecticPointClassExtension
import SymmetricSubgroupAsymptotics.CFSGSymplecticNaturalBilinearClassGeometry
import SymmetricSubgroupAsymptotics.LinearSemidirectTwoOrbitClassBound

/-! The genuine natural symplectic action discharges the pairing and
transitivity premises of the two-orbit inertia theorem. Combined with
the actual affine quotient, this proves a uniform point-stabilizer
class recurrence over every finite field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticPointClassRecurrence
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
open CFSGSymplecticPointAffineHom CFSGSymplecticPointClassExtension
open CFSGSymplecticNaturalBilinearClassGeometry LinearSemidirectCommutingFibres
variable (K : Type) [Field K]

local instance finiteElementary [Finite K] (r : ℕ) : Finite (elementaryRootGroup K r) :=
  Finite.of_injective (fun g : elementaryRootGroup K r => (g.val : Mat K r))
    (by intro g h he; exact Subtype.ext (Units.ext he))

theorem affine_class_card_le [Finite K] (r : ℕ) :
    Nat.card (ConjClasses (AffineGroup (naturalLinearHom K (r+1)))) ≤
      Nat.card (ConjClasses (elementaryRootGroup K (r+1))) +
        Nat.card (ConjClasses (pointStabilizer K r)) := by
  let ρ := naturalLinearHom K (r+1)
  letI := BilinearContragredientDuality.naturalAction ρ
  let e : Index (r+1) → K := Pi.single (Sum.inl 0) 1
  have he : e ≠ 0 := by
    intro hz
    have hh := congrFun hz (Sum.inl 0)
    change (1 : K) = 0 at hh
    exact one_ne_zero hh
  have hpres : ∀ g : elementaryRootGroup K (r+1), ∀ x y : Index (r+1) → K,
      naturalPairing K (r+1) (ρ g x) (ρ g y) = naturalPairing K (r+1) x y := by
    intro g x y
    exact elementary_preserves_pairing (r+1) g x y
  have htrans : ∀ x y : Index (r+1) → K, x ≠ 0 → y ≠ 0 →
      ∃ g : elementaryRootGroup K (r+1), ρ g x = y := by
    intro x y hx hy
    exact exists_map_nonzero K (r+1) (Nat.succ_pos r) x y hx hy
  have hs : MulAction.stabilizer (elementaryRootGroup K (r+1)) e =
      pointStabilizer K r := rfl
  have hc := LinearSemidirectTwoOrbitClassBound.class_card_le
    (naturalPairing K (r+1)) (naturalPairing_nondegenerate K (r+1))
    ρ hpres e he htrans
  rw [hs] at hc
  exact hc

theorem class_card_recurrence [Finite K] (r : ℕ) :
    Nat.card (ConjClasses (pointStabilizer K (r+1))) ≤
      Nat.card K * (Nat.card (ConjClasses (elementaryRootGroup K (r+1))) +
        Nat.card (ConjClasses (pointStabilizer K r))) :=
  (class_card_le_affine K (r+1) (Nat.succ_pos r)).trans
    (Nat.mul_le_mul_left _ (affine_class_card_le K r))

end SymmetricSubgroupAsymptotics.CFSGSymplecticPointClassRecurrence
