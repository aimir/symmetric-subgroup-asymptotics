import SymmetricSubgroupAsymptotics.BinaryEightTop31CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryCoordinateGeneratorFixedCount
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts

/-! Twelve literal axis factors inside the selected31 augmentation kernel.
Each finite test uses128 reversible kernel coordinates or64 actual top
rows. No degree16 source/lift/normal family is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31K45JointCounts
open BinaryEightTop31CoordinateAction
open BinaryRegularEightNaturalRegistry (chart45 charts)

def axisIndex : Fin 12 → Fin 47 := ![0,9,17,20,21,23,26,29,31,37,44,45]
def axes (i : Fin 12) : Σ d, BinaryCoordinateSpace 8 d := charts (axisIndex i)
def fixedBound : Fin 12 → ℕ := ![2,32,8,8,8,8,128,128,128,128,16,128]
def topBound : Fin 12 → ℕ := ![1,16,1,1,1,1,64,64,64,64,2,64]
def centralBound : Fin 12 → ℕ := ![1,2,1,1,1,1,2,2,2,2,2,2]
def derivedExponent : Fin 12 → ℕ := ![8,4,6,6,6,7,2,2,2,3,5,1]
def insideExponent : Fin 12 → ℕ := ![1,2,1,1,1,2,2,2,2,3,2,1]
def outsideExponent : Fin 12 → ℕ := ![0,4,0,0,0,1,6,6,6,7,1,5]

def centralGenerators (t : H) : Prop := ∀ j : Fin 3, generators j*t=t*generators j
instance centralGenerators_decidable (t : H) : Decidable (centralGenerators t) :=
  inferInstanceAs (Decidable (∀ j : Fin 3, generators j*t=t*generators j))

private theorem fixed_counts : ∀ i : Fin 12,
    Fintype.card {a : Fin 7 → ZMod 2 // ∀ j : Fin 3,
      rho (generators j) (chart45.inclusion a)-chart45.inclusion a ∈ (axes i).2.space} =
        fixedBound i := by decide +kernel
private theorem top_counts : ∀ i : Fin 12,
    Fintype.card {r : Fin 64 // ∀ j : Fin 7,
      rho (rowEquiv r) (chart45.inclusion (Pi.single j 1))-
        chart45.inclusion (Pi.single j 1) ∈ (axes i).2.space} = topBound i := by decide +kernel
private theorem central_counts : ∀ i : Fin 12,
    Fintype.card {r : Fin 64 // centralGenerators (rowEquiv r) ∧ ∀ j : Fin 7,
      rho (rowEquiv r) (chart45.inclusion (Pi.single j 1))-
        chart45.inclusion (Pi.single j 1) ∈ (axes i).2.space} = centralBound i := by decide +kernel

theorem fixed_card_le (i : Fin 12) :
    Nat.card {v : V // v ∈ chart45.space ∧ ∀ t : H,
      rho t v-v ∈ (axes i).2.space} ≤ fixedBound i :=
  BinaryCoordinateFixedTopCardBounds.fixed_card_le_coordinate_count rho chart45 (axes i).2
    generators (fixedBound i) (by simpa only [Nat.card_eq_fintype_card] using fixed_counts i)

theorem top_card_le (i : Fin 12) :
    Nat.card {t : H // ∀ v, v ∈ chart45.space → rho t v-v ∈ (axes i).2.space} ≤ topBound i := by
  simpa only [true_and] using BinaryCoordinateFixedTopCardBounds.top_card_le rho chart45
    (axes i).2 rowEquiv (fun _ => True) (topBound i)
      (by simpa only [Nat.card_eq_fintype_card,true_and] using top_counts i)

theorem central_top_card_le (i : Fin 12) :
    Nat.card {t : H // t ∈ Subgroup.center H ∧
      ∀ v, v ∈ chart45.space → rho t v-v ∈ (axes i).2.space} ≤ centralBound i := by
  have hb := BinaryCoordinateFixedTopCardBounds.top_card_le rho chart45 (axes i).2 rowEquiv
    centralGenerators (centralBound i)
      (by simpa only [Nat.card_eq_fintype_card] using central_counts i)
  let f : {t : H // t ∈ Subgroup.center H ∧
      ∀ v, v ∈ chart45.space → rho t v-v ∈ (axes i).2.space} →
      {t : H // centralGenerators t ∧
      ∀ v, v ∈ chart45.space → rho t v-v ∈ (axes i).2.space} :=
    fun t => ⟨t.val,⟨fun j => Subgroup.mem_center_iff.mp t.property.1 (generators j),t.property.2⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    change x.val = y.val
    exact congrArg (fun t => t.val) h
  exact (Nat.card_le_card_of_injective f hf).trans hb

private theorem inside_arithmetic : ∀ i : Fin 12,
    fixedBound i * centralBound i ≤ 2^(axes i).1 * 2^(insideExponent i) := by decide +kernel
private theorem outside_arithmetic : ∀ i : Fin 12,
    fixedBound i * topBound i ≤ 2 * 2^(axes i).1 * 2^(outsideExponent i) := by decide +kernel

theorem inside_capacity (i : Fin 12) :
    Nat.card {v : V // v ∈ chart45.space ∧ ∀ t : H, rho t v-v ∈ (axes i).2.space} *
      Nat.card {t : H // t ∈ Subgroup.center H ∧
        ∀ v, v ∈ chart45.space → rho t v-v ∈ (axes i).2.space} ≤
      Nat.card (axes i).2.space * 2^(insideExponent i) := by
  exact (Nat.mul_le_mul (fixed_card_le i) (central_top_card_le i)).trans
    (by rw [(axes i).2.card]; exact inside_arithmetic i)

theorem outside_capacity (i : Fin 12) :
    Nat.card {v : V // v ∈ chart45.space ∧ ∀ t : H, rho t v-v ∈ (axes i).2.space} *
      Nat.card {t : H // ∀ v, v ∈ chart45.space → rho t v-v ∈ (axes i).2.space} ≤
      2 * Nat.card (axes i).2.space * 2^(outsideExponent i) := by
  exact (Nat.mul_le_mul (fixed_card_le i) (top_card_le i)).trans
    (by rw [(axes i).2.card]; exact outside_arithmetic i)

theorem derived_arithmetic (i : Fin 12) :
    Nat.card (axes i).2.space * 2^(derivedExponent i) = 256 := by
  rw [(axes i).2.card]
  revert i
  decide +kernel

theorem inside_cost : ∀ i : Fin 12, i ≠ 0 → i ≠ 5 →
    2^(derivedExponent i) * 2^(insideExponent i) ≤ 256 ∧ 2^(insideExponent i) ≤ 16 := by
  decide +kernel

theorem outside_cost : ∀ i : Fin 12, (axes i).1 < 5 →
    2^(derivedExponent i) * 2^(outsideExponent i) ≤ 256 ∧ 2^(outsideExponent i) ≤ 16 := by
  decide +kernel
end SymmetricSubgroupAsymptotics.BinaryEightTop31K45JointCounts
