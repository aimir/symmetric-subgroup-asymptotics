import SymmetricSubgroupAsymptotics.BinaryEightTop31CoordinateAction

/-! The actual31 top center is bounded using its certified64 rows and
original three generators; no abstract identification is required. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31GroupBounds
open BinaryEightTop31CoordinateAction

def centralGenerators (t : H) : Prop := ∀ j : Fin 3, generators j*t=t*generators j
instance centralGenerators_decidable (t : H) : Decidable (centralGenerators t) :=
  inferInstanceAs (Decidable (∀ j : Fin 3, generators j*t=t*generators j))
private theorem count : Fintype.card {r : Fin 64 // centralGenerators (rowEquiv r)} = 2 := by
  decide +kernel

theorem center_card_le_two : Nat.card (Subgroup.center H) ≤ 2 := by
  let f : Subgroup.center H → {r : Fin 64 // centralGenerators (rowEquiv r)} := fun t =>
    ⟨rowEquiv.symm t.val,by
      rw [rowEquiv.apply_symm_apply]
      exact fun j => Subgroup.mem_center_iff.mp t.property (generators j)⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact rowEquiv.symm.injective (congrArg Subtype.val h)
  exact (Nat.card_le_card_of_injective f hf).trans_eq (by
    simpa only [Nat.card_eq_fintype_card] using count)
end SymmetricSubgroupAsymptotics.BinaryEightTop31GroupBounds
