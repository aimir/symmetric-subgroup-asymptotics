import SymmetricSubgroupAsymptotics.SymmetricMatrixFunctionalDualOrbit

/-! The exact two-frame bound for a genuine base-field annihilator.
The invariant subspace and the projected subgroup are the actual
supplied J and L; no extension-field linearity of J is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.SymmetricMatrixAnnihilatorTwoFrameIndex

open SymmetricMatrixCongruenceAction SymmetricMatrixQuadraticFunctional
open SymmetricMatrixFunctionalDualOrbit
variable {F K : Type*} [Field F] [Field K] [Algebra F K] (n : ℕ)

/-- Restrict the original functional to the actual K-line through the cross vector. -/
def crossRestriction (ℓ : Module.Dual F (Space (K := K) n)) (x y : Fin n → K) :
    Module.Dual F K :=
  ℓ.comp ((LinearMap.toSpanSingleton K (Space (K := K) n) (cross n x y)).restrictScalars F)

@[simp] theorem crossRestriction_apply (ℓ : Module.Dual F (Space (K := K) n))
    (x y : Fin n → K) (t : K) :
    crossRestriction n ℓ x y t = ℓ (t • cross n x y) := rfl

/-- All factors refer to the same J and L, including when F is just the prime field. -/
theorem two_frame_le_twice_quotient_card_mul_index
    [Finite F] [Finite K] [CharP K 2] (hn : 2 ≤ n)
    (L : Subgroup (GeneralLinear (K := K) n))
    (J : Submodule F (Space (K := K) n))
    (hJ : ∀ A ∈ L, ∀ S ∈ J, congruenceLinearMap n A S ∈ J)
    (x y : Fin n → K) (t : K) (ht : t • cross n x y ∉ J) :
    (Nat.card K - 1) * Nat.card K ^ (n - 2) * (Nat.card K ^ n - Nat.card K) ≤
      2 * (Nat.card (Space (K := K) n ⧸ J) * L.index) := by
  letI : Module.Finite F K := Module.Finite.of_finite
  letI : Module.Finite F (Space (K := K) n) := Module.Finite.of_finite
  obtain ⟨φ, hφ⟩ := InvariantAnnihilatorOrbitIndex.exists_annihilator_nonzero_on
    J (t • cross n x y) ht
  let f := crossRestriction n φ.val x y
  have hf : f ≠ 0 := by
    intro he
    have hz := congrArg (fun a : Module.Dual F K => a t) he
    change φ.val (t • cross n x y) = 0 at hz
    exact hφ hz
  have hlow := two_frame_le_twice_dual_orbit n hn f hf φ.val x y (fun _ => rfl)
  have hupper := InvariantAnnihilatorOrbitIndex.dual_orbit_card_le_quotient_card_mul_index
    (restrictedCongruence (F := F) n) L J
    (fun A hA S hS => hJ A hA S hS) φ
  exact hlow.trans (Nat.mul_le_mul_left 2 hupper)

end SymmetricSubgroupAsymptotics.SymmetricMatrixAnnihilatorTwoFrameIndex
