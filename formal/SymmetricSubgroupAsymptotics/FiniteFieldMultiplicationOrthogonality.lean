import SymmetricSubgroupAsymptotics.FieldFunctionalMultiplicationDuality
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Lean.Elab.Tactic.Omega

/-! Rectangular orthogonality for arbitrary base-field subspaces of a field.
The two subspaces may differ and need not be linear over the extension field.
A proper third subspace containing their products supplies an annihilating
functional; multiplication identifies its orthogonality with dual annihilation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.FiniteFieldMultiplicationOrthogonality

open FieldFunctionalMultiplicationDuality

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

theorem finrank_add_le [Module.Finite F K]
    (C V W : Submodule F K) (hC : C ≠ ⊤)
    (hmul : ∀ a ∈ V, ∀ b ∈ W, a * b ∈ C) :
    Module.finrank F V + Module.finrank F W ≤ Module.finrank F K := by
  obtain ⟨f, hf, hCf⟩ := C.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hC)
  let φ : V →ₗ[F] W.dualAnnihilator :=
    ((multiplicationFunctional f).comp V.subtype).codRestrict W.dualAnnihilator
      (fun a => (W.mem_dualAnnihilator _).mpr (fun b hb => hCf (hmul a a.property b hb)))
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply multiplicationFunctional_injective f hf
    exact congrArg Subtype.val hab
  have hd := LinearMap.finrank_le_finrank_of_injective hφ
  have hs := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

theorem card_mul_le [Finite F] [Finite K]
    (C V W : Submodule F K) (hC : C ≠ ⊤)
    (hmul : ∀ a ∈ V, ∀ b ∈ W, a * b ∈ C) :
    Nat.card V * Nat.card W ≤ Nat.card K := by
  letI : Module.Finite F K := Module.Finite.of_finite
  have hd := finrank_add_le C V W hC hmul
  have hV : Nat.card V = Nat.card F ^ Module.finrank F V :=
    Module.natCard_eq_pow_finrank (K := F) (V := V)
  have hW : Nat.card W = Nat.card F ^ Module.finrank F W :=
    Module.natCard_eq_pow_finrank (K := F) (V := W)
  have hK : Nat.card K = Nat.card F ^ Module.finrank F K :=
    Module.natCard_eq_pow_finrank (K := F) (V := K)
  rw [hV, hW, hK, ← pow_add]
  exact Nat.pow_le_pow_right (Nat.card_pos (α := F)) hd

theorem additive_card_mul_le (p : ℕ) [Fact p.Prime] [CharP K p] [Finite K]
    (C V W : AddSubgroup K) (hC : C ≠ ⊤)
    (hmul : ∀ a ∈ V, ∀ b ∈ W, a * b ∈ C) :
    Nat.card V * Nat.card W ≤ Nat.card K := by
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  have hC' : AddSubgroup.toZModSubmodule p C ≠ ⊤ := by
    intro he
    apply hC
    apply (AddSubgroup.toZModSubmodule p).injective
    simpa using he
  let C' : Submodule (ZMod p) K := AddSubgroup.toZModSubmodule p C
  let V' : Submodule (ZMod p) K := AddSubgroup.toZModSubmodule p V
  let W' : Submodule (ZMod p) K := AddSubgroup.toZModSubmodule p W
  have hm : ∀ a ∈ V', ∀ b ∈ W', a * b ∈ C' := hmul
  exact card_mul_le (F := ZMod p) (K := K) C' V' W' hC' hm

end SymmetricSubgroupAsymptotics.FiniteFieldMultiplicationOrthogonality
