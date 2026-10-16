import SymmetricSubgroupAsymptotics.BinaryFourCyclicLayerRepresentations
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! The common middle-plus-top envelope uses two generator slots.
Its exact chart is the previously checked diagonal quotient module,
retaining two trivial types and two copies of the binary-plane type. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

def localCyclicLinear : Ternary →* (Local ≃ₗ[Scalar] Local) :=
  powersHom 3 localCycle localCycle_cube

def localCyclicRepresentation : Representation Scalar Ternary Local :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation localCyclicLinear

def middleTopEnvelope : Representation Scalar Ternary (Middle × Local) :=
  middleCyclicRepresentation.prod localCyclicRepresentation

def middleTailEquiv : Middle ≃ₗ[Scalar] tailSpace true where
  toFun x := ⟨x, by intro h; cases h⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def middleTopEnvelopeEquiv : middleTopEnvelope.Equiv
    (LinearSemidirectCoprimeSocleBounds.linearRepresentation (quotientLinear true)) where
  toLinearEquiv := middleTailEquiv.prodCongr (LinearEquiv.refl Scalar Local)
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro w
    have hcycle (x : Middle) :
        middleTailEquiv (rawMiddleCycle x) = tailCycle true (middleTailEquiv x) := by
      apply Subtype.ext
      ext i
      fin_cases i <;> rfl
    have hpower : ∀ (n : ℕ) (x : Middle) (y : Local),
        (middleTailEquiv ((rawMiddleCycle ^ n) x), (localCycle ^ n) y) =
          (quotientCycle true ^ n) (middleTailEquiv x, y) := by
      intro n x y
      induction n with
      | zero => rfl
      | succ n ih =>
          simp only [pow_succ', LinearEquiv.mul_apply]
          rw [← ih]
          exact Prod.ext (hcycle _) rfl
    change (middleTailEquiv ((rawMiddleCycle ^ g.toAdd.val) w.1),
        (localCycle ^ g.toAdd.val) w.2) =
      (quotientCycle true ^ g.toAdd.val) (middleTailEquiv w.1, w.2)
    exact hpower _ _ _

theorem middleTopEnvelope_uniform :
    UniformSubrepresentationGeneratorBound middleTopEnvelope 2 := by
  have hcard : Nat.card Ternary = 3 := by
    rw [Nat.card_congr (Multiplicative.toAdd : Ternary ≃ ZMod 3), Nat.card_zmod]
  letI : NeZero (Nat.card Ternary : Scalar) := ⟨by
    rw [hcard]
    change (3 : Scalar) ≠ 0
    decide⟩
  have huniform := RepresentationGeneratedBy.uniform_of_invertible_order
    (k := Scalar) _ (quotientRepresentation_generated true)
  exact huniform.of_injective middleTopEnvelopeEquiv.toIntertwiningMap
    middleTopEnvelopeEquiv.injective

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
