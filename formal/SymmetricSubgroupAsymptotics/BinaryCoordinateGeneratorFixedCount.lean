import SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds

/-! A generator-level fixed-preimage count on the small reversible
kernel coordinates bounds the original full-top fixed-preimage cardinal.
Only an injection is used, so no generator-completeness premise is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds

variable {H J : Type} [Group H] {w k c : ℕ}
    (rho : Representation (ZMod 2) H (Fin w → ZMod 2))
    (K : BinaryCoordinateSpace w k) (C : BinaryCoordinateSpace w c)

theorem fixed_card_le_coordinate_count (generators : J → H) (n : ℕ)
    (hc : Nat.card {a : Fin k → ZMod 2 //
      ∀ j, rho (generators j) (K.inclusion a) - K.inclusion a ∈ C.space} = n) :
    Nat.card {v : Fin w → ZMod 2 // v ∈ K.space ∧
      ∀ t : H, rho t v - v ∈ C.space} ≤ n := by
  let f : {v : Fin w → ZMod 2 // v ∈ K.space ∧
      ∀ t : H, rho t v - v ∈ C.space} →
      {a : Fin k → ZMod 2 //
        ∀ j, rho (generators j) (K.inclusion a) - K.inclusion a ∈ C.space} :=
    fun v => ⟨K.coordinates v.val, by
      rw [(K.mem_iff v.val).mp v.property.1]
      exact fun j => v.property.2 (generators j)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hh := congrArg (fun a : {a : Fin k → ZMod 2 //
      ∀ j, rho (generators j) (K.inclusion a) - K.inclusion a ∈ C.space} =>
      K.inclusion a.val) h
    exact ((K.mem_iff x.val).mp x.property.1).symm.trans
      (hh.trans ((K.mem_iff y.val).mp y.property.1))
  exact (Nat.card_le_card_of_injective f hf).trans_eq hc

end SymmetricSubgroupAsymptotics.BinaryCoordinateFixedTopCardBounds
