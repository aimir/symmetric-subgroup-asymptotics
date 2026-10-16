import SymmetricSubgroupAsymptotics.BinaryFourAugmentationActions

/-! Exact middle-layer coordinates for the six-dimensional augmentation
module. The kernel of the displayed projection is the literal diagonal
binary plane. On the quotient, Klein acts trivially and the ternary
operator is the direct sum of two trivial coordinates and localCycle.
All statements are identities on the existing augmentation module. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

abbrev Middle := Fin 4 → Scalar

def middleProjection : Coordinates →ₗ[Scalar] Middle where
  toFun x := ![x 2, x 3, x 4, x 5]
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

def middleLift : Middle →ₗ[Scalar] Coordinates where
  toFun x := ![0, 0, x 0, x 1, x 2, x 3]
  map_add' := by intro x y; ext i; fin_cases i <;> simp
  map_smul' := by intro a x; ext i; fin_cases i <;> simp

theorem middleProjection_lift (x : Middle) :
    middleProjection (middleLift x) = x := by
  ext i
  fin_cases i <;> rfl

theorem middleProjection_surjective : Function.Surjective middleProjection :=
  fun x => ⟨middleLift x, middleProjection_lift x⟩

theorem middleProjection_kernel (x : Coordinates) :
    x ∈ LinearMap.ker middleProjection ↔
      x 2 = 0 ∧ x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 := by
  change middleProjection x = 0 ↔ _
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩
  · rintro ⟨h2, h3, h4, h5⟩
    ext i
    fin_cases i <;> assumption

theorem middleProjection_klein (p : Klein) (x : Coordinates) :
    middleProjection (kleinLinear p x) = middleProjection x := by
  ext i
  fin_cases i <;> rfl

/-- Coordinates 0,1 are fixed scalars; coordinates 2,3 form W. -/
def middleChart : Middle ≃ₗ[Scalar] Middle where
  toFun x := ![x 0 + x 1 + x 2 + x 3, x 3,
    x 1 + x 2 + x 3, x 0 + x 2]
  invFun y := ![y 0 + y 2, y 0 + y 1 + y 3,
    y 0 + y 2 + y 3, y 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by intro x y; ext i; fin_cases i <;> simp <;> ring
  map_smul' := by intro a x; ext i; fin_cases i <;> simp <;> ring

def middleCycle (x : Middle) : Middle := ![x 0, x 1, x 2 + x 3, x 2]

theorem middleChart_c (x : Coordinates) :
    middleChart (middleProjection (c x)) =
      middleCycle (middleChart (middleProjection x)) := by
  revert x
  decide +kernel

/-- The common Klein fixed space in the radical is exactly its bottom
plane. This statement uses only the two literal Klein generators. -/
theorem augmentation_klein_fixed_iff (x : Coordinates) :
    u x = x ∧ v x = x ↔ x ∈ LinearMap.ker middleProjection := by
  rw [middleProjection_kernel]
  revert x
  decide +kernel

/-- The ambient induced module's augmentation is the literal sum of
its four local planes. Its kernel is precisely the existing radical chart. -/
def ambientAugmentation : Module →ₗ[Scalar] Local where
  toFun w := w 0 + w 1 + w 2 + w 3
  map_add' := by intro x y; ext i; simp; ring
  map_smul' := by intro a x; ext i; simp; ring

theorem ambientAugmentation_decode (x : Coordinates) :
    ambientAugmentation (decode x) = 0 := by
  revert x
  decide +kernel

theorem decode_encode_iff (w : Module) :
    decode (encode w) = w ↔ ambientAugmentation w = 0 := by
  revert w
  decide +kernel

theorem ambient_radical_exact (w : Module) :
    w ∈ LinearMap.ker ambientAugmentation ↔ ∃ x : Coordinates, decode x = w := by
  change ambientAugmentation w = 0 ↔ _
  constructor
  · intro hw
    exact ⟨encode w, (decode_encode_iff w).mpr hw⟩
  · rintro ⟨x, rfl⟩
    exact ambientAugmentation_decode x

/-- Klein fixes exactly the diagonal copy of the local plane in the
ambient induced module. Both block permutations are the original ones. -/
theorem ambient_klein_fixed_iff (w : Module) :
    (∀ b, w (blockU b) = w b) ∧ (∀ b, w (blockV b) = w b) ↔
      ∃ a : Local, ∀ b, w b = a := by
  revert w
  decide +kernel

/-- The ambient induced ternary generator combines the original block
cycle and its local binary-plane cycle. -/
def ambientCycle (w : Module) : Module :=
  fun b => localCycle (w (blockC⁻¹ b))

theorem decode_u (x : Coordinates) :
    decode (u x) = fun b => decode x (blockU b) := by
  revert x
  decide +kernel

theorem decode_v (x : Coordinates) :
    decode (v x) = fun b => decode x (blockV b) := by
  revert x
  decide +kernel

theorem decode_c (x : Coordinates) :
    decode (c x) = ambientCycle (decode x) := by
  revert x
  decide +kernel

theorem ambientAugmentation_cycle (w : Module) :
    ambientAugmentation (ambientCycle w) = localCycle (ambientAugmentation w) := by
  revert w
  decide +kernel

/-- The actual characteristic-two Klein differences on the ambient
module. Their commuting square-zero operators give radical length three. -/
def ambientDifferenceU (w : Module) : Module := fun b => w (blockU b) + w b

def ambientDifferenceV (w : Module) : Module := fun b => w (blockV b) + w b

theorem ambientDifferenceU_square (w : Module) :
    ambientDifferenceU (ambientDifferenceU w) = 0 := by
  revert w
  decide +kernel

theorem ambientDifferenceV_square (w : Module) :
    ambientDifferenceV (ambientDifferenceV w) = 0 := by
  revert w
  decide +kernel

theorem ambientDifferences_commute (w : Module) :
    ambientDifferenceU (ambientDifferenceV w) =
      ambientDifferenceV (ambientDifferenceU w) := by
  revert w
  decide +kernel

theorem ambientDoubleDifference (w : Module) :
    ambientDifferenceU (ambientDifferenceV w) =
      fun _ => ambientAugmentation w := by
  revert w
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
