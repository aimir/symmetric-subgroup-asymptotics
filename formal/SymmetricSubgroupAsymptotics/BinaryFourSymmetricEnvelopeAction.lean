import SymmetricSubgroupAsymptotics.BinaryFourSymmetricEnvelopeProjectors
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalSymmetricInducedChart

/-! The actual S4 quotient action on the seven-dimensional common socle
envelope. Klein acts trivially; the retained ternary and odd actions are
kept simultaneously. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions SemidirectProduct

def envelopeCycleEquiv : SymmetricEnvelope ≃ₗ[Scalar] SymmetricEnvelope where
  toFun := envelopeCycle
  invFun x := envelopeCycle (envelopeCycle x)
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by
    intro x y
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> exact map_add localCycle _ _
  map_smul' := by
    intro a x
    apply Prod.ext
    · rfl
    · apply Prod.ext <;> exact map_smul localCycle _ _

def envelopeReflectionEquiv : SymmetricEnvelope ≃ₗ[Scalar] SymmetricEnvelope where
  toFun := envelopeReflection
  invFun := envelopeReflection
  left_inv := by decide +kernel
  right_inv := by decide +kernel
  map_add' := by
    intro x y
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · apply Prod.ext <;> ext i <;> fin_cases i <;> simp [envelopeReflection] <;> ring
  map_smul' := by
    intro a x
    apply Prod.ext
    · ext i; fin_cases i <;> rfl
    · apply Prod.ext <;> ext i <;> fin_cases i <;> simp [envelopeReflection] <;> ring

theorem envelopeCycle_cube : envelopeCycleEquiv ^ 3 = 1 := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

theorem envelopeReflection_square : envelopeReflectionEquiv ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

def envelopeTernary : Ternary →* (SymmetricEnvelope ≃ₗ[Scalar] SymmetricEnvelope) :=
  powersHom 3 envelopeCycleEquiv envelopeCycle_cube

def envelopeBinary : Binary →* (SymmetricEnvelope ≃ₗ[Scalar] SymmetricEnvelope) :=
  powersHom 2 envelopeReflectionEquiv envelopeReflection_square

def envelopeEven : Complement →* (SymmetricEnvelope ≃ₗ[Scalar] SymmetricEnvelope) :=
  envelopeTernary.comp SemidirectProduct.rightHom

theorem envelopeCompatibility (b : Binary) :
    envelopeEven.comp (complementBinaryAction b).toMonoidHom =
      (MulAut.conj (envelopeBinary b)).toMonoidHom.comp envelopeEven := by
  apply MonoidHom.ext
  intro r
  apply LinearEquiv.ext
  intro x
  rcases r with ⟨p, z⟩
  revert b p z x
  decide +kernel

def symmetricEnvelopeLinear : SymmetricComplement →*
    (SymmetricEnvelope ≃ₗ[Scalar] SymmetricEnvelope) :=
  SemidirectProduct.lift envelopeEven envelopeBinary envelopeCompatibility

def symmetricEnvelopeRepresentation : Representation Scalar SymmetricComplement SymmetricEnvelope :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation symmetricEnvelopeLinear

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
