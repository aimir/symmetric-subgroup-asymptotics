import SymmetricSubgroupAsymptotics.BinaryFourMiddleSectionFactor
import SymmetricSubgroupAsymptotics.BinaryFourAugmentationQuotientCoordinates

/-! Actual cyclic representations on the induced ambient module and
its middle layer. The displayed coordinate projection is an intertwiner
on every actual invariant submodule of the radical. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

def ambientCycleEquiv : Module ≃ₗ[Scalar] Module where
  toFun := ambientCycle
  invFun w := ambientCycle (ambientCycle w)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by
    intro x y
    ext b i
    fin_cases i <;> simp [ambientCycle, localCycle] <;> ring
  map_smul' := by
    intro a x
    ext b i
    fin_cases i <;> simp [ambientCycle, localCycle] <;> ring

theorem ambientCycleEquiv_cube : ambientCycleEquiv ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro w
  revert w
  decide +kernel

def rawMiddleCycle : Middle ≃ₗ[Scalar] Middle where
  toFun x := ![x 2, x 0 + x 3, x 1 + x 3, x 3]
  invFun x := ![x 1 + x 3, x 2 + x 3, x 0, x 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring

theorem rawMiddleCycle_cube : rawMiddleCycle ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro w
  revert w
  decide +kernel

def ambientCyclicLinear : Ternary →* (Module ≃ₗ[Scalar] Module) :=
  powersHom 3 ambientCycleEquiv ambientCycleEquiv_cube

def middleCyclicLinear : Ternary →* (Middle ≃ₗ[Scalar] Middle) :=
  powersHom 3 rawMiddleCycle rawMiddleCycle_cube

def ambientCyclicRepresentation : Representation Scalar Ternary Module :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation ambientCyclicLinear

def middleCyclicRepresentation : Representation Scalar Ternary Middle :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation middleCyclicLinear

def ambientMiddleCoordinates : Module →ₗ[Scalar] Middle :=
  middleProjection.comp encodeLinear

theorem ambientAugmentation_power (n : ℕ) (w : Module) :
    ambientAugmentation ((ambientCycleEquiv ^ n) w) =
      (localCycle ^ n) (ambientAugmentation w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', pow_succ']
      change ambientAugmentation (ambientCycle ((ambientCycleEquiv ^ n) w)) = _
      rw [ambientAugmentation_cycle, ih]
      rfl

theorem ambientMiddleCoordinates_cycle (w : Module)
    (hw : ambientAugmentation w = 0) :
    ambientMiddleCoordinates (ambientCycle w) = rawMiddleCycle (ambientMiddleCoordinates w) := by
  have exactIdentity : ∀ w : Module, ambientAugmentation w = 0 →
      ambientMiddleCoordinates (ambientCycle w) =
        rawMiddleCycle (ambientMiddleCoordinates w) := by decide +kernel
  exact exactIdentity w hw

theorem ambientMiddleCoordinates_power (n : ℕ) (w : Module)
    (hw : ambientAugmentation w = 0) :
    ambientMiddleCoordinates ((ambientCycleEquiv ^ n) w) =
      (rawMiddleCycle ^ n) (ambientMiddleCoordinates w) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hn : ambientAugmentation ((ambientCycleEquiv ^ n) w) = 0 := by
        rw [ambientAugmentation_power, hw, map_zero]
      rw [pow_succ', pow_succ']
      change ambientMiddleCoordinates (ambientCycle ((ambientCycleEquiv ^ n) w)) = _
      rw [ambientMiddleCoordinates_cycle _ hn, ih]
      rfl

def radicalCyclic : Subrepresentation ambientCyclicRepresentation where
  toSubmodule := LinearMap.ker ambientAugmentation
  apply_mem_toSubmodule g w hw := by
    change ambientAugmentation ((ambientCycleEquiv ^ g.toAdd.val) w) = 0
    rw [ambientAugmentation_power, show ambientAugmentation w = 0 from hw, map_zero]

def subrepresentationMiddleIntertwiner
    (E : Subrepresentation ambientCyclicRepresentation) (hE : E ≤ radicalCyclic) :
    E.toRepresentation.IntertwiningMap middleCyclicRepresentation where
  toLinearMap := submoduleMiddleMap E.toSubmodule
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    change ambientMiddleCoordinates ((ambientCycleEquiv ^ g.toAdd.val) (w : Module)) =
      (rawMiddleCycle ^ g.toAdd.val) (ambientMiddleCoordinates (w : Module))
    exact ambientMiddleCoordinates_power _ _ (hE w.2)

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
