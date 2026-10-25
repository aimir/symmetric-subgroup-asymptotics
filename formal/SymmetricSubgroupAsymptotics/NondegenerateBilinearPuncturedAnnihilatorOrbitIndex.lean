import SymmetricSubgroupAsymptotics.NondegenerateBilinearAnnihilatorOrbitIndex
import SymmetricSubgroupAsymptotics.PuncturedAnnihilatorScalarWordIndex
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! The zero functional is excluded from the actual annihilator orbit.
The resulting estimate retains precisely the supplied prime-field J
and projected L. The integer companion pays the binary orbit24 head
without enumerating any matrices, subgroups, or actions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NondegenerateBilinearPuncturedAnnihilatorOrbitIndex
open NondegenerateBilinearAnnihilatorOrbitIndex

variable {F K V G : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V] [Group G]

theorem natural_orbit_lower_le_punctured_quotient_card_mul_index
    [Finite F] [Finite K] [Finite G] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (ρ : G →* V ≃ₗ[K] V)
    (hρ : ∀ g : G, ∀ v w : V, B (ρ g v) (ρ g w) = B v w)
    (b : ℕ)
    (hb : ∀ v : V, v ≠ 0 → b ≤
      Nat.card (BilinearNaturalDualOrbitTransfer.naturalOrbit ρ v))
    (L : Subgroup G) (J : Submodule F V)
    (hJ : ∀ g ∈ L, ∀ v ∈ J,
      FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := F) ρ g v ∈ J)
    (z : V) (hz : z ∉ J) : b ≤ (Nat.card (V ⧸ J)-1) * L.index := by
  letI : Finite V := Module.finite_of_finite K
  letI : Module.Finite F K := Module.Finite.of_finite
  letI : Module.Finite F V := Module.Finite.of_finite
  obtain ⟨φ, hφ⟩ := InvariantAnnihilatorOrbitIndex.exists_annihilator_nonzero_on J z hz
  let f := scalarRestriction (K := K) φ.val z
  have hf : f ≠ 0 := by
    intro he
    have h := congrArg (fun l : Module.Dual F K => l 1) he
    change φ.val ((1 : K) • z) = 0 at h
    rw [one_smul] at h
    exact hφ h
  obtain ⟨A, hA, _⟩ := FiniteFieldFunctionalLift.exists_unique_linear_lift f hf φ.val
  have hmap : FiniteFieldFunctionalOrbitTransfer.functionalMap f A = φ.val :=
    LinearMap.ext (fun v => (hA v).symm)
  have hA0 : A ≠ 0 := by
    intro he
    have hAz : φ.val z = 0 := by
      simpa only [he, LinearMap.zero_apply, map_zero] using hA z
    exact hφ hAz
  let v := (B.toDual hB).symm A
  have hvA : B v = A := (B.toDual hB).apply_symm_apply A
  have hv : v ≠ 0 := by
    intro he
    apply hA0
    simpa only [he, map_zero] using hvA.symm
  have horbit := BilinearNaturalDualOrbitTransfer.restricted_dualOrbit_card_eq
    B hB ρ hρ f hf v
  rw [hvA, hmap] at horbit
  have hlow : b ≤ Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit
      (FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := F) ρ) φ.val) :=
    (hb v hv).trans_eq horbit.symm
  have hφ0 : φ.val ≠ 0 := by
    intro he
    exact hφ (by rw [he]; rfl)
  have hupper := PuncturedAnnihilatorScalarWordIndex.dual_orbit_card_le_punctured_quotient_card_mul_index
    (FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := F) ρ) L J hJ φ hφ0
  exact hlow.trans hupper

theorem thirtyTwo_le_binary_multiple (k l : ℕ) (hl : 0 < l)
    (horbit : 24 ≤ (2^k-1)*l) : 32 ≤ 2^k*l := by
  by_cases hk : 5 ≤ k
  · exact ((by decide : 32 ≤ (2:ℕ)^5).trans
      (Nat.pow_le_pow_right (by decide) hk)).trans
        (Nat.le_mul_of_pos_right _ hl)
  · have hk4 : k ≤ 4 := by omega
    interval_cases k <;> norm_num at horbit <;> omega

end SymmetricSubgroupAsymptotics.NondegenerateBilinearPuncturedAnnihilatorOrbitIndex
