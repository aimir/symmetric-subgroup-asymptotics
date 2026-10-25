import SymmetricSubgroupAsymptotics.ScalarDualAnnihilatorOrbitIndex

/-! Scalar words inside an actual prime-field linear action suffice for
the full nonzero dual orbit. Other elements need not act by field scalars. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarWordDualAnnihilatorOrbitIndex
open FieldFunctionalMultiplicationDuality InvariantAnnihilatorOrbitIndex
variable {F K T : Type*} [Field F] [Field K] [Algebra F K] [Group T]

theorem dual_orbit_card_ge [Finite F] [Finite K] [Module.Finite F K]
    (ρ : T →* K ≃ₗ[F] K)
    (hscalar : ∀ a : Kˣ, ∃ t : T, ∀ x : K, ρ t x = (a : K)*x)
    (f : Module.Dual F K) (hf : f ≠ 0) :
    Nat.card K - 1 ≤ Nat.card (dualOrbit ρ f) := by
  letI : Finite (Module.Dual F K) := Module.finite_of_finite F
  let e : Kˣ → dualOrbit ρ f := fun a =>
    ⟨multiplicationFunctional f (a : K), by
      obtain ⟨t,ht⟩ := hscalar a
      refine ⟨t⁻¹, ?_⟩
      apply LinearMap.ext
      intro x
      change f (ρ (t⁻¹)⁻¹ x) = f ((a : K)*x)
      rw [inv_inv,ht]⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Units.ext
    exact multiplicationFunctional_injective f hf (congrArg Subtype.val hab)
  calc
    Nat.card K - 1 = Nat.card Kˣ := (Nat.card_units K).symm
    _ ≤ Nat.card (dualOrbit ρ f) := Nat.card_le_card_of_injective e he

theorem quotient_card_mul_index_ge [Finite F] [Finite K] [Finite T] [Module.Finite F K]
    (ρ : T →* K ≃ₗ[F] K)
    (hscalar : ∀ a : Kˣ, ∃ t : T, ∀ x : K, ρ t x = (a : K)*x)
    (L : Subgroup T) (C : Submodule F K)
    (hC : ∀ t ∈ L, ∀ x ∈ C, ρ t x ∈ C)
    (f : C.dualAnnihilator) (hf : f.val ≠ 0) :
    Nat.card K - 1 ≤ Nat.card (K ⧸ C)*L.index :=
  (dual_orbit_card_ge ρ hscalar f.val hf).trans
    (dual_orbit_card_le_quotient_card_mul_index ρ L C hC f)

end SymmetricSubgroupAsymptotics.ScalarWordDualAnnihilatorOrbitIndex
