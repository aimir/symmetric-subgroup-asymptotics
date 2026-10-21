import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedFactor
import Mathlib.SetTheory.Cardinal.Finite

/-! Generic sparse fixed-vector and finite top-predicate cardinal bounds.
Both factors retain the same coordinate denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds
variable {H I J : Type} [Group H] [Finite H] [Finite I]
    {w k c d : ℕ} (rho : Representation (ZMod 2) H (Fin w → ZMod 2))
    (K : BinaryCoordinateSpace w k) (C : BinaryCoordinateSpace w c)

theorem fixed_card_le (D : BinaryCoordinateSpace w d) (generators : J → H)
    (hfixed : ∀ v, v ∈ D.space ↔ v ∈ K.space ∧
      ∀ j, rho (generators j) v - v ∈ C.space) :
    Nat.card {v : Fin w → ZMod 2 // v ∈ K.space ∧
      ∀ t : H, rho t v - v ∈ C.space} ≤ 2 ^ d := by
  let f : {v : Fin w → ZMod 2 // v ∈ K.space ∧
      ∀ t : H, rho t v - v ∈ C.space} → D.space := fun v =>
    ⟨v.val, (hfixed v.val).mpr ⟨v.property.1, fun j => v.property.2 (generators j)⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun v : D.space => v.val) h)
  exact (Nat.card_le_card_of_injective f hf).trans_eq D.card

theorem top_card_le (e : I ≃ H) (P : H → Prop) (n : ℕ)
    (hc : Nat.card {i : I // P (e i) ∧ ∀ j : Fin k,
      rho (e i) (K.inclusion (Pi.single j 1)) -
        K.inclusion (Pi.single j 1) ∈ C.space} = n) :
    Nat.card {t : H // P t ∧ ∀ v, v ∈ K.space → rho t v - v ∈ C.space} ≤ n := by
  let f : {t : H // P t ∧ ∀ v, v ∈ K.space → rho t v - v ∈ C.space} →
      {i : I // P (e i) ∧ ∀ j : Fin k,
      rho (e i) (K.inclusion (Pi.single j 1)) - K.inclusion (Pi.single j 1) ∈ C.space} :=
    fun t => ⟨e.symm t.val, by
      rw [e.apply_symm_apply]
      exact ⟨t.property.1, fun j => t.property.2 _ ⟨_, rfl⟩⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg (fun i : {i : I // P (e i) ∧ ∀ j : Fin k,
      rho (e i) (K.inclusion (Pi.single j 1)) -
        K.inclusion (Pi.single j 1) ∈ C.space} => i.val) h
  exact (Nat.card_le_card_of_injective f hf).trans_eq hc

end SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds
