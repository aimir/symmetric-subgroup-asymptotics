import SymmetricSubgroupAsymptotics.SubgroupInvariantSetOrbitIndex
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! The dual orbit of an actual annihilator vector is bounded by the
actual quotient size and the index of the same subgroup preserving the
subspace. No larger-field linearity of an additive stabilizer is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex

variable {F G V : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V]

/-- Literal contragredient action associated with the given linear action. -/
abbrev dualAction (ρ : G →* V ≃ₗ[F] V) : MulAction G (Module.Dual F V) where
  smul g φ := φ.comp (ρ g⁻¹).toLinearMap
  one_smul φ := by
    apply LinearMap.ext
    intro v
    change φ ((ρ (1 : G)⁻¹) v) = φ v
    rw [inv_one, map_one]
    rfl
  mul_smul g h φ := by
    apply LinearMap.ext
    intro v
    change φ ((ρ (g * h)⁻¹) v) = φ ((ρ h⁻¹) ((ρ g⁻¹) v))
    rw [mul_inv_rev, map_mul]
    rfl

/-- The orbit as an explicit set, with no hidden choice of action. -/
def dualOrbit (ρ : G →* V ≃ₗ[F] V) (φ : Module.Dual F V) : Set (Module.Dual F V) :=
  {ψ | ∃ g : G, φ.comp (ρ g⁻¹).toLinearMap = ψ}

/-- Every vector outside the subspace is detected by an actual member
of its annihilator. -/
theorem exists_annihilator_nonzero_on (J : Submodule F V) (z : V) (hz : z ∉ J) :
    ∃ φ : J.dualAnnihilator, φ.val z ≠ 0 := by
  obtain ⟨φ, hzφ, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hz inferInstance
  refine ⟨⟨φ, ?_⟩, hzφ⟩
  rw [Submodule.mem_dualAnnihilator]
  intro v hv
  have hm : φ v ∈ J.map φ := Submodule.mem_map.mpr ⟨v, hv, rfl⟩
  rw [hφ] at hm
  exact (Submodule.mem_bot F).mp hm

/-- The same actual subgroup preserves J and pays the index factor.
In particular J may be only a prime-field subspace of a larger field. -/
theorem dual_orbit_card_le_quotient_card_mul_index
    [Finite F] [Finite G] [Module.Finite F V]
    (ρ : G →* V ≃ₗ[F] V) (L : Subgroup G) (J : Submodule F V)
    (hJ : ∀ g ∈ L, ∀ v ∈ J, ρ g v ∈ J)
    (φ : J.dualAnnihilator) :
    Nat.card (dualOrbit ρ φ.val) ≤ Nat.card (V ⧸ J) * L.index := by
  letI : MulAction G (Module.Dual F V) := dualAction ρ
  letI : Finite (Module.Dual F V) := Module.finite_of_finite F
  have hA : ∀ g : L, ∀ ψ ∈ (J.dualAnnihilator : Set (Module.Dual F V)),
      g • ψ ∈ (J.dualAnnihilator : Set (Module.Dual F V)) := by
    intro g ψ hψ
    change ψ.comp (ρ g.val⁻¹).toLinearMap ∈ J.dualAnnihilator
    change ψ ∈ J.dualAnnihilator at hψ
    rw [Submodule.mem_dualAnnihilator] at hψ ⊢
    intro v hv
    exact hψ _ (hJ g.val⁻¹ (L.inv_mem g.property) v hv)
  have h := SubgroupInvariantSetOrbitIndex.orbit_card_le_invariant_set_mul_index
    L (J.dualAnnihilator : Set (Module.Dual F V)) φ.val φ.property hA
  have hc : Nat.card J.dualAnnihilator = Nat.card (V ⧸ J) :=
    (Nat.card_congr (Subspace.quotEquivAnnihilator J).toEquiv).symm
  have h' : Nat.card (dualOrbit ρ φ.val) ≤ Nat.card J.dualAnnihilator * L.index := h
  rw [hc] at h'
  exact h'

end SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex
