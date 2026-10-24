import SymmetricSubgroupAsymptotics.FiniteFieldFunctionalOrbitTransfer
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! A preserved nondegenerate bilinear form identifies actual natural
and contragredient orbits. Composition with one fixed base-field
functional then transfers the same orbit after restriction of scalars. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BilinearNaturalDualOrbitTransfer

variable {K V G : Type*} [Field K] [AddCommGroup V] [Module K V] [Group G]

def naturalOrbit (ρ : G →* V ≃ₗ[K] V) (v : V) : Set V :=
  {w | ∃ g : G, ρ g v = w}

theorem bilinear_covariance (B : LinearMap.BilinForm K V)
    (ρ : G →* V ≃ₗ[K] V)
    (hρ : ∀ g : G, ∀ v w : V, B (ρ g v) (ρ g w) = B v w)
    (g : G) (v : V) :
    B (ρ g v) = (B v).comp (ρ g⁻¹).toLinearMap := by
  apply LinearMap.ext
  intro w
  have hi : ρ g (ρ g⁻¹ w) = w := by
    change ((ρ g) * (ρ g⁻¹)) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have h := hρ g v (ρ g⁻¹ w)
  rw [hi] at h
  exact h

def orbitEquiv (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (ρ : G →* V ≃ₗ[K] V)
    (hρ : ∀ g : G, ∀ v w : V, B (ρ g v) (ρ g w) = B v w) (v : V) :
    naturalOrbit ρ v ≃ InvariantAnnihilatorOrbitIndex.dualOrbit ρ (B v) := by
  let e : naturalOrbit ρ v → InvariantAnnihilatorOrbitIndex.dualOrbit ρ (B v) :=
    fun w => ⟨B w.val, by
      obtain ⟨g, hg⟩ := w.property
      refine ⟨g, ?_⟩
      rw [← bilinear_covariance B ρ hρ, hg]⟩
  have hbinj : Function.Injective B := LinearMap.ker_eq_bot.mp hB.ker_eq_bot
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · intro w z he
    apply Subtype.ext
    apply hbinj
    exact congrArg (fun φ : InvariantAnnihilatorOrbitIndex.dualOrbit ρ (B v) => φ.val) he
  · intro φ
    obtain ⟨g, hg⟩ := φ.property
    refine ⟨⟨ρ g v, ⟨g, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change B (ρ g v) = φ.val
    exact (bilinear_covariance B ρ hρ g v).trans hg

theorem orbit_card_eq (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (ρ : G →* V ≃ₗ[K] V)
    (hρ : ∀ g : G, ∀ v w : V, B (ρ g v) (ρ g w) = B v w) (v : V) :
    Nat.card (naturalOrbit ρ v) =
      Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit ρ (B v)) :=
  Nat.card_congr (orbitEquiv B hB ρ hρ v)

theorem restricted_dualOrbit_card_eq
    {F : Type*} [Field F] [Algebra F K] [Module F V] [IsScalarTower F K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (ρ : G →* V ≃ₗ[K] V)
    (hρ : ∀ g : G, ∀ v w : V, B (ρ g v) (ρ g w) = B v w)
    (f : Module.Dual F K) (hf : f ≠ 0) (v : V) :
    Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit
      (FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := F) ρ)
      (FiniteFieldFunctionalOrbitTransfer.functionalMap f (B v))) =
        Nat.card (naturalOrbit ρ v) :=
  (FiniteFieldFunctionalOrbitTransfer.dualOrbit_card_eq ρ f hf (B v)).symm.trans
    (orbit_card_eq B hB ρ hρ v).symm

end SymmetricSubgroupAsymptotics.BilinearNaturalDualOrbitTransfer
