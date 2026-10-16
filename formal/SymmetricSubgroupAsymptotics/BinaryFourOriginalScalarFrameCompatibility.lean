import SymmetricSubgroupAsymptotics.BinaryFourOriginalMiddleSourceScalarTransport
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopScalarEnvelope

/-! The original lower and top charts use the same transported scalar
representation and the same actual original quotient map. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

open BinaryFourSymmetricBlockActions

variable {G H : Type} [Group G] [Group H]

theorem s4_original_frame_comp {p : ℕ} (hp : p = 2)
    (e : H ≃* SymmetricComplement) (pi : G →* H) :
    (BinaryFourOriginalScalarCharts.s4Frame hp e).comp pi =
      canonicalFullAt hp (e.toMonoidHom.comp pi) := by
  subst p
  rfl

theorem a4_original_frame_comp {p : ℕ} (hp : p = 2)
    (e : H ≃* Complement) (pi : G →* H) :
    (BinaryFourOriginalScalarCharts.a4Frame hp e).comp pi =
      canonicalFullAt hp (SemidirectProduct.inl.comp (e.toMonoidHom.comp pi)) := by
  subst p
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro x
  change BinaryFourFullBlockCoordinates.fullComplementLinear (e (pi g)) x =
    symmetricLinear (SemidirectProduct.inl (e (pi g))) x
  rw [symmetricLinear, SemidirectProduct.lift_inl]

theorem original_envelope_scalar_compatibility {p : ℕ} (hp : p = 2)
    (gamma : G →* SymmetricComplement) :
    BinaryFourCanonicalTopScalarEnvelope.representation hp gamma =
      canonicalEnvelopeAt hp gamma := by
  subst p
  rfl

end SymmetricSubgroupAsymptotics.BinaryFourBlockAugmentation

end
