import SymmetricSubgroupAsymptotics.BilinearNaturalDualOrbitTransfer

/-! A genuine base-field annihilator inherits the natural orbit lower
bound via the actual preserved nondegenerate form. Both the subspace and
the subgroup in the resulting index bound are the supplied actual J,L. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.NondegenerateBilinearAnnihilatorOrbitIndex

variable {F K V G : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V] [Group G]

def scalarRestriction (ℓ : Module.Dual F V) (z : V) : Module.Dual F K :=
  ℓ.comp ((LinearMap.toSpanSingleton K V z).restrictScalars F)

@[simp] theorem scalarRestriction_apply (ℓ : Module.Dual F V) (z : V) (t : K) :
    scalarRestriction ℓ z t = ℓ (t • z) := rfl

theorem natural_orbit_lower_le_quotient_card_mul_index
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
    (z : V) (hz : z ∉ J) : b ≤ Nat.card (V ⧸ J) * L.index := by
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
  have hupper := InvariantAnnihilatorOrbitIndex.dual_orbit_card_le_quotient_card_mul_index
    (FiniteFieldFunctionalOrbitTransfer.restrictedRepresentation (F := F) ρ) L J hJ φ
  exact hlow.trans hupper

end SymmetricSubgroupAsymptotics.NondegenerateBilinearAnnihilatorOrbitIndex
