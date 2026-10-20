import SymmetricSubgroupAsymptotics.BinaryFourAugmentationMiddleChart
import SymmetricSubgroupAsymptotics.CommutingSquareZeroNakayama

/-! The ambient augmentation is the unique simple top: a submodule
stable under the actual Klein differences and mapping onto that top is
already the whole original induced module. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

def ambientDifferenceULinear : Module →ₗ[Scalar] Module where
  toFun := ambientDifferenceU
  map_add' := by intro x y; ext b i; simp [ambientDifferenceU]; ring
  map_smul' := by intro a x; ext b i; simp [ambientDifferenceU]; ring

def ambientDifferenceVLinear : Module →ₗ[Scalar] Module where
  toFun := ambientDifferenceV
  map_add' := by intro x y; ext b i; simp [ambientDifferenceV]; ring
  map_smul' := by intro a x; ext b i; simp [ambientDifferenceV]; ring

def radicalUSource (w : Module) : Module := ![w 2, w 3, 0, 0]
def radicalVSource (w : Module) : Module := ![w 0 + w 2, 0, 0, 0]

theorem radical_difference_decomposition (w : Module)
    (hw : ambientAugmentation w = 0) :
    w = ambientDifferenceU (radicalUSource w) +
      ambientDifferenceV (radicalVSource w) := by
  have exactIdentity : ∀ w : Module, ambientAugmentation w = 0 →
      w = ambientDifferenceU (radicalUSource w) +
        ambientDifferenceV (radicalVSource w) := by decide +kernel
  exact exactIdentity w hw

theorem eq_top_of_augmentation_surjective
    (E : Submodule Scalar Module)
    (hU : ∀ w ∈ E, ambientDifferenceU w ∈ E)
    (hV : ∀ w ∈ E, ambientDifferenceV w ∈ E)
    (honto : ∀ a : Local, ∃ e ∈ E, ambientAugmentation e = a) : E = ⊤ := by
  apply eq_top_of_commuting_square_zero_generators
    ambientDifferenceULinear ambientDifferenceVLinear
    ambientDifferenceU_square ambientDifferenceV_square ambientDifferences_commute
    E hU hV
  intro x
  obtain ⟨e, he, heaug⟩ := honto (ambientAugmentation x)
  have hw : ambientAugmentation (x - e) = 0 := by
    rw [map_sub, heaug, sub_self]
  have hd := radical_difference_decomposition (x - e) hw
  refine ⟨e, he, radicalUSource (x - e), radicalVSource (x - e), ?_⟩
  change x = e + ambientDifferenceU _ + ambientDifferenceV _
  calc
    x = e + (x - e) := by abel
    _ = e + ambientDifferenceU (radicalUSource (x - e)) +
        ambientDifferenceV (radicalVSource (x - e)) :=
      (congrArg (fun y => e + y) hd).trans (add_assoc _ _ _).symm

theorem localCycle_generates (x : Local) (hx : x ≠ 0) (y : Local) :
    ∃ a b : Scalar, a • x + b • localCycle x = y := by
  have exactIdentity : ∀ x : Local, x ≠ 0 → ∀ y : Local,
      ∃ a b : Scalar, a • x + b • localCycle x = y := by decide +kernel
  exact exactIdentity x hx y

/-- Every actual proper A4-invariant submodule lies in the actual radical.
The hypotheses are only invariance under the three displayed generators. -/
theorem proper_submodule_le_augmentation_kernel
    (E : Submodule Scalar Module) (hproper : E ≠ ⊤)
    (hU : ∀ w ∈ E, ambientDifferenceU w ∈ E)
    (hV : ∀ w ∈ E, ambientDifferenceV w ∈ E)
    (hC : ∀ w ∈ E, ambientCycle w ∈ E) :
    E ≤ LinearMap.ker ambientAugmentation := by
  intro w hw
  change ambientAugmentation w = 0
  by_contra hnonzero
  apply hproper
  apply eq_top_of_augmentation_surjective E hU hV
  intro y
  obtain ⟨a, b, hab⟩ := localCycle_generates (ambientAugmentation w) hnonzero y
  refine ⟨a • w + b • ambientCycle w,
    E.add_mem (E.smul_mem a hw) (E.smul_mem b (hC w hw)), ?_⟩
  rw [map_add, map_smul, map_smul, ambientAugmentation_cycle]
  exact hab

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
