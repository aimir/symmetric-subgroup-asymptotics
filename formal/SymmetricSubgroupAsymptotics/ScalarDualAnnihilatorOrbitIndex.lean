import SymmetricSubgroupAsymptotics.FieldFunctionalMultiplicationDuality
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex
import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.Module.Equiv.Basic

/-! A surjective ACTUAL scalar action has a full nonzero orbit on the
prime-field dual. An invariant subspace pays that orbit with its actual
quotient cardinality and the index of the SAME preserving subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ScalarDualAnnihilatorOrbitIndex
open FieldFunctionalMultiplicationDuality InvariantAnnihilatorOrbitIndex
variable {F K T : Type*} [Field F] [Field K] [Algebra F K] [Group T]

def scalarAction (s : T →* Kˣ) : T →* K ≃ₗ[F] K :=
  (Units.mulLeftLinearEquiv F K).comp s

theorem dual_orbit_card_ge [Finite F] [Finite K] [Module.Finite F K]
    (s : T →* Kˣ) (hs : Function.Surjective s)
    (f : Module.Dual F K) (hf : f ≠ 0) :
    Nat.card K - 1 ≤ Nat.card (dualOrbit (scalarAction (F := F) s) f) := by
  letI : Finite (Module.Dual F K) := Module.finite_of_finite F
  let e : Kˣ → dualOrbit (scalarAction (F := F) s) f := fun a =>
    ⟨multiplicationFunctional f (a : K), by
      obtain ⟨t, ht⟩ := hs a⁻¹
      refine ⟨t, ?_⟩
      have hh : s t⁻¹ = a := by rw [map_inv, ht, inv_inv]
      apply LinearMap.ext
      intro x
      change f ((s t⁻¹ : K) * x) = f ((a : K) * x)
      rw [hh]⟩
  have he : Function.Injective e := by
    intro a b hab
    apply Units.ext
    exact multiplicationFunctional_injective f hf (congrArg Subtype.val hab)
  calc
    Nat.card K - 1 = Nat.card Kˣ := (Nat.card_units K).symm
    _ ≤ Nat.card (dualOrbit (scalarAction (F := F) s) f) := Nat.card_le_card_of_injective e he

theorem quotient_card_mul_index_ge [Finite F] [Finite K] [Finite T] [Module.Finite F K]
    (s : T →* Kˣ) (hs : Function.Surjective s)
    (L : Subgroup T) (C : Submodule F K)
    (hC : ∀ t ∈ L, ∀ x ∈ C, scalarAction (F := F) s t x ∈ C)
    (f : C.dualAnnihilator) (hf : f.val ≠ 0) :
    Nat.card K - 1 ≤ Nat.card (K ⧸ C) * L.index :=
  (dual_orbit_card_ge s hs f.val hf).trans
    (dual_orbit_card_le_quotient_card_mul_index (scalarAction (F := F) s) L C hC f)

end SymmetricSubgroupAsymptotics.ScalarDualAnnihilatorOrbitIndex
