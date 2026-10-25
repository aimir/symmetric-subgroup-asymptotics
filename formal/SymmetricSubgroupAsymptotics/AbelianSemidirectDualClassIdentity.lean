import SymmetricSubgroupAsymptotics.AbelianSemidirectLinearFibreDuality
import SymmetricSubgroupAsymptotics.LinearContragredientSmallSpaceAction
import SymmetricSubgroupAsymptotics.CommutingPairJointFixedDoubleCount
import Mathlib.Algebra.Group.TypeTags.Finite

/-! An exact class identity for an actual abelian semidirect product.
Commuting fibres are dualized with both literal projected elements, then
the SAME dual action is counted through its actual stabilizers. Only the
positive cardinal of the original translation group is cancelled. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AbelianSemidirectDualClassIdentity
open AbelianActionClassBound AbelianSemidirectLinearFibreDuality
open LinearContragredientSmallSpaceAction CommutingPairJointFixedDoubleCount

variable {K N G : Type*} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)]

def dualStabilizer (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (ℓ : Module.Dual K (Additive N)) : Subgroup G :=
  letI : MulAction G (Module.Dual K (Additive N)) :=
    MulAction.compHom _ (contragredient ρ)
  MulAction.stabilizer G ℓ

local instance [Finite K] [Finite N] : Finite (Module.Dual K (Additive N)) :=
  Finite.of_injective
    (fun ℓ : Module.Dual K (Additive N) => (ℓ : Additive N → K)) DFunLike.coe_injective

local instance [Finite K] [Finite N] : Fintype (Module.Dual K (Additive N)) :=
  Fintype.ofFinite _

theorem class_weighted_identity [Finite K] [Finite N] [Finite G]
    (φ : G →* MulAut N) (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n) = Additive.ofMul (φ g n)) :
    Nat.card G * Nat.card (ConjClasses (N ⋊[φ] G)) =
      ∑ ℓ : Module.Dual K (Additive N),
        Nat.card (dualStabilizer ρ ℓ) * Nat.card (ConjClasses (dualStabilizer ρ ℓ)) := by
  letI : FiniteDimensional K (Additive N) := Module.Finite.of_finite
  letI : MulAction G (Module.Dual K (Additive N)) :=
    MulAction.compHom _ (contragredient ρ)
  letI : Finite (N ⋊[φ] G) :=
    Finite.of_equiv (N × G) SemidirectProduct.equivProd.symm
  letI : Fintype (CommutingPairs G) := Fintype.ofFinite _
  have hfibre (p : CommutingPairs G) :
      Nat.card (AbelianActionCommutingFibreBound.Fibre φ p.val.1 p.val.2) = Nat.card N *
        Nat.card {ℓ : Module.Dual K (Additive N) //
          p.val.1 • ℓ = ℓ ∧ p.val.2 • ℓ = ℓ} := by
    let e : {ℓ : Module.Dual K (Additive N) //
        (∀ v : Additive N, ℓ (ρ p.val.1 v) = ℓ v) ∧
        (∀ v : Additive N, ℓ (ρ p.val.2 v) = ℓ v)} ≃
        {ℓ : Module.Dual K (Additive N) // p.val.1 • ℓ = ℓ ∧ p.val.2 • ℓ = ℓ} := {
      toFun := fun ℓ => ⟨ℓ.val,
        (fixed_iff ρ p.val.1 ℓ.val).mpr ℓ.property.1,
        (fixed_iff ρ p.val.2 ℓ.val).mpr ℓ.property.2⟩
      invFun := fun ℓ => ⟨ℓ.val,
        (fixed_iff ρ p.val.1 ℓ.val).mp ℓ.property.1,
        (fixed_iff ρ p.val.2 ℓ.val).mp ℓ.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    exact (card_commuting_fibre φ ρ hcompat p.val.1 p.val.2 p.property).trans
      (congrArg (Nat.card N * ·) (Nat.card_congr e))
  have hcomm : Nat.card (CommutingPairs (N ⋊[φ] G)) = Nat.card N *
      Nat.card (JointFixed (G := G) (X := Module.Dual K (Additive N))) := by
    rw [Nat.card_congr (AbelianActionClassBound.commutingEquiv φ), Nat.card_sigma]
    simp_rw [hfibre]
    rw [← Finset.mul_sum, ← Nat.card_sigma]
  have hscaled := hcomm
  rw [card_comm_eq_card_conjClasses_mul_card, SemidirectProduct.card] at hscaled
  have hcancel : Nat.card N * (Nat.card G * Nat.card (ConjClasses (N ⋊[φ] G))) =
      Nat.card N * Nat.card (JointFixed (G := G) (X := Module.Dual K (Additive N))) := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hscaled
  calc
    _ = Nat.card (JointFixed (G := G) (X := Module.Dual K (Additive N))) :=
      Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := N)) hcancel
    _ = _ := joint_fixed_card

end SymmetricSubgroupAsymptotics.AbelianSemidirectDualClassIdentity
