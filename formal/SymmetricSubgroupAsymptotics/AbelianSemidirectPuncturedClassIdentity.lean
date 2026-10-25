import SymmetricSubgroupAsymptotics.AbelianSemidirectDualClassIdentity
import SymmetricSubgroupAsymptotics.LinearPuncturedJointFixedCount

/-! If the ACTUAL contragredient action is transitive on its nonzero
functionals, the original semidirect class count is exactly the sum of
the projected group's class count and that of its actual functional
stabilizer. The two stabilizers are identified inside the same group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.AbelianSemidirectPuncturedClassIdentity
open AbelianSemidirectDualClassIdentity LinearContragredientSmallSpaceAction
open LinearPuncturedJointFixedCount CommutingPairJointFixedDoubleCount

variable {K N G : Type*} [Field K] [CommGroup N] [Group G]
    [Module K (Additive N)] [Finite K] [Finite N] [Finite G]

theorem class_card_eq_add_dual_stabilizer
    (φ : G →* MulAut N) (ρ : G →* (Additive N ≃ₗ[K] Additive N))
    (hcompat : ∀ (g : G) (n : N), ρ g (Additive.ofMul n) = Additive.ofMul (φ g n))
    (htrans : ∀ ℓ m : Module.Dual K (Additive N), ℓ ≠ 0 → m ≠ 0 →
      ∃ g : G, contragredient ρ g ℓ = m)
    (ℓ₀ : {ℓ : Module.Dual K (Additive N) // ℓ ≠ 0}) :
    Nat.card (ConjClasses (N ⋊[φ] G)) =
      Nat.card (ConjClasses G) + Nat.card (ConjClasses (dualStabilizer ρ ℓ₀.val)) := by
  letI : Finite (Module.Dual K (Additive N)) := Finite.of_injective
    (fun ℓ : Module.Dual K (Additive N) => (ℓ : Additive N → K)) DFunLike.coe_injective
  letI : Fintype (Module.Dual K (Additive N)) := Fintype.ofFinite _
  letI : MulAction G (Module.Dual K (Additive N)) :=
    MulAction.compHom _ (contragredient ρ)
  letI : MulAction G {ℓ : Module.Dual K (Additive N) // ℓ ≠ 0} :=
    puncturedAction (contragredient ρ)
  have hstab : dualStabilizer ρ ℓ₀.val = puncturedStabilizer (contragredient ρ) ℓ₀ := by
    apply Subgroup.ext
    intro g
    change contragredient ρ g ℓ₀.val = ℓ₀.val ↔ g • ℓ₀ = ℓ₀
    constructor
    · intro hg
      apply Subtype.ext
      exact hg
    · intro hg
      exact congrArg Subtype.val hg
  have hjoint : Nat.card (JointFixed (G := G) (X := Module.Dual K (Additive N))) =
      Nat.card G * (Nat.card (ConjClasses G) +
        Nat.card (ConjClasses (dualStabilizer ρ ℓ₀.val))) := by
    rw [hstab]
    change Nat.card ((p : AbelianActionClassBound.CommutingPairs G) ×
      {ℓ : Module.Dual K (Additive N) //
        contragredient ρ p.val.1 ℓ = ℓ ∧ contragredient ρ p.val.2 ℓ = ℓ}) = _
    exact joint_fixed_card_eq_of_punctured_transitive (contragredient ρ) htrans ℓ₀
  have hweighted := class_weighted_identity φ ρ hcompat
  have hsum : (∑ ℓ : Module.Dual K (Additive N),
      Nat.card (dualStabilizer ρ ℓ) * Nat.card (ConjClasses (dualStabilizer ρ ℓ))) =
      Nat.card (JointFixed (G := G) (X := Module.Dual K (Additive N))) :=
    joint_fixed_card.symm
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
    (hweighted.trans (hsum.trans hjoint))

end SymmetricSubgroupAsymptotics.AbelianSemidirectPuncturedClassIdentity
