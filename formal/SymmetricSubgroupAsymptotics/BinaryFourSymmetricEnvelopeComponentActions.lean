import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeAction
import SymmetricSubgroupAsymptotics.BinaryFourFullBlockQuotient

/-! The two actual component actions of the S4 socle envelope. The
three-dimensional component is inflated from the odd quotient, whereas
the active component retains a two-copy C3 action. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions BinaryFourFullBlockCoordinates SemidirectProduct

def trivialEnvelopeRepresentation : Representation Scalar SymmetricComplement (Fin 3 → Scalar) :=
  BinaryJordanPlusTrivialUniformGenerators.rho.comp SemidirectProduct.rightHom

theorem trivialEnvelope_uniform :
    UniformSubrepresentationGeneratorBound trivialEnvelopeRepresentation 2 := by
  apply UniformSubrepresentationGeneratorBound.comp_of_surjective
    BinaryJordanPlusTrivialUniformGenerators.rho SemidirectProduct.rightHom
  · intro b
    exact ⟨SemidirectProduct.inr b, rfl⟩
  · exact BinaryJordanPlusTrivialUniformGenerators.uniform

def activeEnvelopeReflection : DoubleLocal ≃ₗ[Scalar] DoubleLocal where
  toFun x := (![x.1 0 + x.1 1, x.1 1], ![x.2 1, x.2 0])
  invFun x := (![x.1 0 + x.1 1, x.1 1], ![x.2 1, x.2 0])
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by
    intro x y
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a x
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp <;> ring

theorem activeEnvelopeReflection_square : activeEnvelopeReflection ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

def activeEnvelopeBinary : Binary →* (DoubleLocal ≃ₗ[Scalar] DoubleLocal) :=
  powersHom 2 activeEnvelopeReflection activeEnvelopeReflection_square

def activeEnvelopeEven : Complement →* (DoubleLocal ≃ₗ[Scalar] DoubleLocal) :=
  doubleLinear.comp SemidirectProduct.rightHom

theorem activeEnvelopeCompatibility (b : Binary) :
    activeEnvelopeEven.comp (complementBinaryAction b).toMonoidHom =
      (MulAut.conj (activeEnvelopeBinary b)).toMonoidHom.comp activeEnvelopeEven := by
  apply MonoidHom.ext
  intro r
  apply LinearEquiv.ext
  intro x
  rcases r with ⟨p, z⟩
  revert b p z x
  decide +kernel

def activeEnvelopeLinear : SymmetricComplement →* (DoubleLocal ≃ₗ[Scalar] DoubleLocal) :=
  SemidirectProduct.lift activeEnvelopeEven activeEnvelopeBinary activeEnvelopeCompatibility

def activeEnvelopeRepresentation : Representation Scalar SymmetricComplement DoubleLocal :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation activeEnvelopeLinear

def envelopeTernaryInclusion : Ternary →* SymmetricComplement :=
  SemidirectProduct.inl.comp SemidirectProduct.inr

theorem activeEnvelope_uniform :
    UniformSubrepresentationGeneratorBound activeEnvelopeRepresentation 2 := by
  apply UniformSubrepresentationGeneratorBound.of_comp
    activeEnvelopeRepresentation envelopeTernaryInclusion
  have heq : activeEnvelopeRepresentation.comp envelopeTernaryInclusion =
      LinearSemidirectCoprimeSocleBounds.linearRepresentation doubleLinear := by
    apply MonoidHom.ext
    intro z
    apply LinearMap.ext
    intro x
    rfl
  rw [heq]
  exact doubleRepresentation_uniform

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
