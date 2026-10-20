import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinaryMiddleSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinaryTopModuleMap
import SymmetricSubgroupAsymptotics.RepresentationSemisimpleSurjectiveInflation

/-! Two generators for the FULL actual binary socle of each original
retained quotient in the zero-core four-by-four geometry. Central trivial
constituents remain in the target, and the original denominator is kept. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

open BinaryFourBlockAugmentation

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveAffineDegreeFourOriginalFullBinarySocleCapacity_localFact1 : Fact P.p.Prime := ⟨P.p_prime⟩

local instance originalFullBinarySocleCapacity_scalarModule
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    _root_.Module (ZMod P.p) (DegreeFourFullBinarySocleChart block P N).V :=
  (DegreeFourFullBinarySocleChart block P N).module

local instance originalFullBinarySocleCapacity_inflatedModule
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    _root_.Module (ZMod P.p)[preE7NonPairAction w U]
      (degreeFourOriginalBinarySocleInflated block P N).asModule :=
  Representation.instModuleMonoidAlgebraAsModule
    (degreeFourOriginalBinarySocleInflated block P N)

include block P

theorem degreeFourOriginalFullBinarySocleInflated_isSemisimple
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    IsSemisimpleModule (ZMod P.p)[preE7NonPairAction w U]
      (degreeFourOriginalBinarySocleInflated block P N).asModule := by
  let Q := DegreeFourRetainedQuotient N
  let A := DegreeFourFullBinarySocle block P N
  let C := DegreeFourFullBinarySocleChart block P N
  letI : _root_.Module (ZMod P.p) C.V := C.module
  let sigma : Representation (ZMod P.p) (Q ⧸ A) C.V := C.quotientRepresentation.ρ
  let t := degreeFourFullBinarySocleTopMap block P N
  have ht : Function.Surjective t :=
    (QuotientGroup.mk'_surjective A).comp (QuotientGroup.mk'_surjective N.1)
  letI : IsSemisimpleModule (ZMod P.p)[Q ⧸ A] sigma.asModule :=
    selectedPrimeSoclePart_quotientRepresentation_isSemisimple P.p
      (G := Q) (degreeFourFullBinarySelector (w := w) (U := U) N)
  exact representation_isSemisimpleModule_comp t ht sigma

namespace DegreeFourS4OriginalPointChart

variable (C : DegreeFourS4OriginalPointChart block)
include C

set_option maxHeartbeats 1000000 in
theorem originalFullBinarySocle_generated_le_two
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    RepresentationGeneratedBy (degreeFourOriginalBinarySocleInflated block P N) 2 := by
  let hp := degreeFour_profilePrime_eq_two block P hr
  let rho : Representation (ZMod P.p) (preE7NonPairAction w U)
      (DegreeFourFullBinarySocleChart block P N).V :=
    degreeFourOriginalBinarySocleInflated block P N
  let T : Subrepresentation rho := degreeFourOriginalBinaryTargetInflated block P N
  letI : IsSemisimpleModule (ZMod P.p)[preE7NonPairAction w U] rho.asModule :=
    degreeFourOriginalFullBinarySocleInflated_isSemisimple (block := block) (P := P) N
  let gamma : preE7NonPairAction w U →* BinaryFourSymmetricBlockActions.SymmetricComplement :=
    canonicalMap (block := block) (P := P) (C := C) hr hD
  have hS : Nonempty (OriginalMiddleSourceAt hp gamma T.toRepresentation) :=
    originalBinaryMiddleSource (block := block) (P := P) (C := C) hr hD N
  have hTop : ∃ j : (rho.asModule ⧸ T.asSubmodule) →ₗ[
      (ZMod P.p)[preE7NonPairAction w U]] (canonicalEnvelopeAt hp gamma).asModule,
      Function.Injective j ∧ ∀ x,
        let y := (canonicalEnvelopeAt hp gamma).asModuleEquiv (j x)
        y.1 0 = 0 ∧ y.1 1 = 0 ∧ y.2.1 = 0 := by
    simpa only [original_envelope_scalar_compatibility,
      BinaryFourCanonicalTopScalarEnvelope.Support] using
      (originalBinaryTopModuleMap (block := block) (P := P) (C := C) hr hD N)
  obtain ⟨S⟩ := hS
  obtain ⟨j, hj, hs⟩ := hTop
  have hFinal : RepresentationGeneratedBy rho 2 :=
    s4_original_socle_generated_at hp gamma
      (canonicalMap_surjective (block := block) (P := P) (C := C) hr hD) rho T S j hj hs
  exact hFinal

end DegreeFourS4OriginalPointChart

namespace DegreeFourA4OriginalPointChart

variable (C : DegreeFourA4OriginalPointChart block)
include C

set_option maxHeartbeats 1000000 in
theorem originalFullBinarySocle_generated_le_two
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    RepresentationGeneratedBy (degreeFourOriginalBinarySocleInflated block P N) 2 := by
  let hp := degreeFour_profilePrime_eq_two block P hr
  let rho : Representation (ZMod P.p) (preE7NonPairAction w U)
      (DegreeFourFullBinarySocleChart block P N).V :=
    degreeFourOriginalBinarySocleInflated block P N
  let T : Subrepresentation rho := degreeFourOriginalBinaryTargetInflated block P N
  let gamma := ((groupEquiv (block := block) (P := P) (C := C) hr hD)).toMonoidHom.comp (QuotientGroup.mk' (E block P))
  have hgamma : Function.Surjective gamma :=
    ((groupEquiv (block := block) (P := P) (C := C) hr hD)).surjective.comp (QuotientGroup.mk'_surjective (E block P))
  letI : IsSemisimpleModule (ZMod P.p)[preE7NonPairAction w U] rho.asModule :=
    degreeFourOriginalFullBinarySocleInflated_isSemisimple (block := block) (P := P) N
  have hS : Nonempty (OriginalMiddleSourceAt hp
      (SemidirectProduct.inl.comp gamma) T.toRepresentation) :=
    originalBinaryMiddleSource (block := block) (P := P) (C := C) hr hD N
  have hTop : ∃ j : (rho.asModule ⧸ T.asSubmodule) →ₗ[
      (ZMod P.p)[preE7NonPairAction w U]]
      (canonicalEnvelopeAt hp (SemidirectProduct.inl.comp gamma)).asModule,
      Function.Injective j ∧
        (∀ x, let y := (canonicalEnvelopeAt hp
          (SemidirectProduct.inl.comp gamma)).asModuleEquiv (j x)
          y.1 0 = 0 ∧ y.1 1 = 0 ∧ y.2.1 = 0) ∧
        (∀ x, ((canonicalEnvelopeAt hp
          (SemidirectProduct.inl.comp gamma)).asModuleEquiv (j x)).1 2 = 0) := by
    simpa only [original_envelope_scalar_compatibility,
      BinaryFourCanonicalTopScalarEnvelope.Support] using
      (originalBinaryTopModuleMap (block := block) (P := P) (C := C) hr hD N)
  obtain ⟨S⟩ := hS
  obtain ⟨j, hj, hs, hz⟩ := hTop
  have hFinal : RepresentationGeneratedBy rho 2 :=
    a4_original_socle_generated_at hp gamma hgamma rho T S j hj hs hz
  exact hFinal

end DegreeFourA4OriginalPointChart

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
