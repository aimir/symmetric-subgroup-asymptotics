import SymmetricSubgroupAsymptotics.BinaryEightTop29CoordinateAction

/-! A small original-top center bound, on the same certified64 rows and
five literal original generators. No quotient-center substitution is made. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop29GroupBounds
open BinaryEightTop29CoordinateAction

def centralGenerators (t : H) : Prop := ∀ j : Fin 5,
  generators j * t = t * generators j
instance centralGenerators_decidable (t : H) : Decidable (centralGenerators t) :=
  inferInstanceAs (Decidable (∀ j : Fin 5, generators j * t = t * generators j))

private theorem central_count : Fintype.card {i : Fin 64 //
    centralGenerators (rowEquiv i)} = 2 := by decide +kernel

theorem center_card_le_two : Nat.card (Subgroup.center H) ≤ 2 := by
  let f : Subgroup.center H → {i : Fin 64 // centralGenerators (rowEquiv i)} :=
    fun t => ⟨rowEquiv.symm t.val, by
      rw [rowEquiv.apply_symm_apply]
      exact fun j => Subgroup.mem_center_iff.mp t.property (generators j)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply rowEquiv.symm.injective
    exact congrArg (fun i : {i : Fin 64 // centralGenerators (rowEquiv i)} => i.val) h
  exact (Nat.card_le_card_of_injective f hf).trans_eq (by
    simpa only [Nat.card_eq_fintype_card] using central_count)

end SymmetricSubgroupAsymptotics.BinaryEightTop29GroupBounds
