import SymmetricSubgroupAsymptotics.BinaryEightTop29CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryCoordinateGeneratorFixedCount
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

/-! ONE selected kernel/axis pilot. All factors concern original8T29,
the already checked K30 and the SAME checked axis23. Small coordinates
replace a whole ambient module/normal enumeration. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop29K30Axis23Capacity
open BinaryEightTop29CoordinateAction
open BinaryRegularEightNaturalRegistry (chart30 chart23)

theorem fixed_count : Fintype.card {a : Fin 5 → ZMod 2 //
    ∀ j : Fin 5, rho (generators j) (chart30.inclusion a) -
      chart30.inclusion a ∈ chart23.space} = 4 := by decide +kernel

theorem top_count : Fintype.card {i : Fin 64 // ∀ j : Fin 5,
    rho (rowEquiv i) (chart30.inclusion (Pi.single j 1)) -
      chart30.inclusion (Pi.single j 1) ∈ chart23.space} = 2 := by decide +kernel

def centralGenerators (t : H) : Prop := ∀ j : Fin 5,
  generators j * t = t * generators j
instance centralGenerators_decidable (t : H) : Decidable (centralGenerators t) :=
  inferInstanceAs (Decidable (∀ j : Fin 5, generators j * t = t * generators j))

theorem central_top_count : Fintype.card {i : Fin 64 // centralGenerators (rowEquiv i) ∧
    ∀ j : Fin 5, rho (rowEquiv i) (chart30.inclusion (Pi.single j 1)) -
      chart30.inclusion (Pi.single j 1) ∈ chart23.space} = 2 := by decide +kernel

theorem central_coordinate_capacity :
    Nat.card {v : V // v ∈ chart30.space ∧
      ∀ t : H, rho t v - v ∈ chart23.space} *
    Nat.card {t : H // t ∈ Subgroup.center H ∧
      ∀ v, v ∈ chart30.space → rho t v - v ∈ chart23.space} ≤
      4 * Nat.card chart23.space := by
  have hf : Nat.card {v : V // v ∈ chart30.space ∧
      ∀ t : H, rho t v - v ∈ chart23.space} ≤ 4 :=
    BinaryCoordinateFixedTopCardBounds.fixed_card_le_coordinate_count
      rho chart30 chart23 generators 4 (by
        simpa only [Nat.card_eq_fintype_card] using fixed_count)
  have ht0 := BinaryCoordinateFixedTopCardBounds.top_card_le rho chart30 chart23
    rowEquiv centralGenerators 2 (by
      simpa only [Nat.card_eq_fintype_card] using central_top_count)
  let f : {t : H // t ∈ Subgroup.center H ∧
      ∀ v, v ∈ chart30.space → rho t v - v ∈ chart23.space} →
    {t : H // centralGenerators t ∧
      ∀ v, v ∈ chart30.space → rho t v - v ∈ chart23.space} :=
    fun t => ⟨t.val, ⟨fun j => Subgroup.mem_center_iff.mp t.property.1 (generators j),
      t.property.2⟩⟩
  have hf0 : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun t : {t : H // centralGenerators t ∧
      ∀ v, v ∈ chart30.space → rho t v - v ∈ chart23.space} => t.val) h
  have ht := (Nat.card_le_card_of_injective f hf0).trans ht0
  exact (Nat.mul_le_mul hf ht).trans (by rw [chart23.card]; decide)

theorem coordinate_capacity :
    Nat.card {v : V // v ∈ chart30.space ∧
      ∀ t : H, rho t v - v ∈ chart23.space} *
    Nat.card {t : H // ∀ v, v ∈ chart30.space → rho t v - v ∈ chart23.space} ≤
      4 * Nat.card chart23.space := by
  have hf : Nat.card {v : V // v ∈ chart30.space ∧
      ∀ t : H, rho t v - v ∈ chart23.space} ≤ 4 :=
    BinaryCoordinateFixedTopCardBounds.fixed_card_le_coordinate_count
      rho chart30 chart23 generators 4 (by
        simpa only [Nat.card_eq_fintype_card] using fixed_count)
  have ht : Nat.card {t : H // ∀ v, v ∈ chart30.space →
      rho t v - v ∈ chart23.space} ≤ 2 := by
    simpa only [true_and] using
      BinaryCoordinateFixedTopCardBounds.top_card_le rho chart30 chart23
        rowEquiv (fun _ => True) 2 (by
          simpa only [Nat.card_eq_fintype_card, true_and] using top_count)
  exact (Nat.mul_le_mul hf ht).trans (by rw [chart23.card]; decide)

end SymmetricSubgroupAsymptotics.BinaryEightTop29K30Axis23Capacity
