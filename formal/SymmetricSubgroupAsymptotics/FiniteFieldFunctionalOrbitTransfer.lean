import SymmetricSubgroupAsymptotics.FiniteFieldFunctionalLift
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex

/-! A fixed nonzero base-field functional transfers the actual entire
contragredient orbit of a larger-field linear functional. The original
annihilator need only be linear over the base field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.FiniteFieldFunctionalOrbitTransfer

variable {F K V G : Type*} [Field F] [Field K] [Algebra F K]
  [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower F K V]
  [Group G]

/-- Composition with one fixed nonzero base-field functional. -/
def functionalMap (f : Module.Dual F K) (L : Module.Dual K V) : Module.Dual F V :=
  f.comp (L.restrictScalars F)

@[simp] theorem functionalMap_apply (f : Module.Dual F K)
    (L : Module.Dual K V) (v : V) : functionalMap f L v = f (L v) := rfl

/-- Scalar multiples of every vector separate the larger-field functionals. -/
theorem functionalMap_injective (f : Module.Dual F K) (hf : f ≠ 0) :
    Function.Injective (functionalMap (V := V) f) := by
  intro L M h
  apply LinearMap.ext
  intro v
  apply FieldFunctionalMultiplicationDuality.multiplicationFunctional_injective f hf
  apply LinearMap.ext
  intro t
  have ht := congrArg (fun φ : Module.Dual F V => φ (t • v)) h
  change f (L v * t) = f (M v * t)
  simpa only [functionalMap_apply, map_smul, smul_eq_mul, mul_comm] using ht

theorem functionalMap_surjective [Module.Finite F K] [Module.Finite K V]
    (f : Module.Dual F K) (hf : f ≠ 0) :
    Function.Surjective (functionalMap (V := V) f) := by
  intro φ
  obtain ⟨L, hL, _⟩ := FiniteFieldFunctionalLift.exists_unique_linear_lift f hf φ
  refine ⟨L, LinearMap.ext (fun v => (hL v).symm)⟩

/-- Restrict the given actual representation, rather than choosing a new action. -/
def restrictedRepresentation (ρ : G →* V ≃ₗ[K] V) : G →* V ≃ₗ[F] V where
  toFun g := (ρ g).restrictScalars F
  map_one' := by
    apply LinearEquiv.ext
    intro v
    change (ρ 1) v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro v
    change (ρ (g * h)) v = (ρ g) ((ρ h) v)
    rw [map_mul]
    rfl

theorem functionalMap_comp (f : Module.Dual F K) (L : Module.Dual K V)
    (e : V ≃ₗ[K] V) :
    functionalMap f (L.comp e.toLinearMap) =
      (functionalMap f L).comp (e.restrictScalars F).toLinearMap := by
  apply LinearMap.ext
  intro v
  rfl

/-- The actual two orbits are equivalent, even without finite-dimensionality. -/
def dualOrbitEquiv (ρ : G →* V ≃ₗ[K] V)
    (f : Module.Dual F K) (hf : f ≠ 0) (L : Module.Dual K V) :
    InvariantAnnihilatorOrbitIndex.dualOrbit ρ L ≃
      InvariantAnnihilatorOrbitIndex.dualOrbit
        (restrictedRepresentation (F := F) ρ) (functionalMap f L) := by
  let e : InvariantAnnihilatorOrbitIndex.dualOrbit ρ L →
      InvariantAnnihilatorOrbitIndex.dualOrbit
        (restrictedRepresentation (F := F) ρ) (functionalMap f L) := fun ψ =>
    ⟨functionalMap f ψ.val, by
      obtain ⟨g, hg⟩ := ψ.property
      refine ⟨g, ?_⟩
      change (functionalMap f L).comp ((ρ g⁻¹).restrictScalars F).toLinearMap = _
      rw [← functionalMap_comp, hg]⟩
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · intro ψ χ he
    apply Subtype.ext
    apply functionalMap_injective f hf
    exact congrArg (fun φ => φ.val) he
  · intro φ
    obtain ⟨g, hg⟩ := φ.property
    refine ⟨⟨L.comp (ρ g⁻¹).toLinearMap, ⟨g, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    change functionalMap f (L.comp (ρ g⁻¹).toLinearMap) = φ.val
    rw [functionalMap_comp]
    exact hg

theorem dualOrbit_card_eq (ρ : G →* V ≃ₗ[K] V)
    (f : Module.Dual F K) (hf : f ≠ 0) (L : Module.Dual K V) :
    Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit ρ L) =
      Nat.card (InvariantAnnihilatorOrbitIndex.dualOrbit
        (restrictedRepresentation (F := F) ρ) (functionalMap f L)) :=
  Nat.card_congr (dualOrbitEquiv ρ f hf L)

end SymmetricSubgroupAsymptotics.FiniteFieldFunctionalOrbitTransfer
