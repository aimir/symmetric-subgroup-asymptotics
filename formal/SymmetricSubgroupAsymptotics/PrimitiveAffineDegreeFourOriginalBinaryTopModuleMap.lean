import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinaryTopEnvelope
import SymmetricSubgroupAsymptotics.RepresentationQuotientModuleEquiv

/-! Final group-algebra-linear top maps for the ORIGINAL socle quotient.
The domain is the exact quotient requested by the common-envelope capacity
engine; support and injectivity are retained through identity coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]
local instance originalBinaryTopModuleMapPrime : Fact P.p.Prime := ⟨P.p_prime⟩

local instance originalBinaryTopModuleMapSocleModule
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Module (ZMod P.p) (DegreeFourFullBinarySocleChart block P N).V :=
  (DegreeFourFullBinarySocleChart block P N).module

abbrev degreeFourOriginalBinarySocleInflated
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Representation (ZMod P.p) (preE7NonPairAction w U)
      (DegreeFourFullBinarySocleChart block P N).V :=
  (DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ.comp
    (degreeFourFullBinarySocleTopMap block P N)

abbrev degreeFourOriginalBinaryTargetInflated
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  ActualWreathAffineCapacity.subrepresentationComp
    (degreeFourFullBinarySocleTopMap block P N)
    (DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ
    (DegreeFourFullBinaryTargetSection block P N)

namespace DegreeFourS4OriginalPointChart
variable (C : DegreeFourS4OriginalPointChart block)

theorem originalBinaryTopModuleMap
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    ∃ j : ((degreeFourOriginalBinarySocleInflated block P N).asModule ⧸
        (degreeFourOriginalBinaryTargetInflated block P N).asSubmodule) →ₗ[
          (ZMod P.p)[preE7NonPairAction w U]]
      (BinaryFourCanonicalTopScalarEnvelope.representation
        (degreeFour_profilePrime_eq_two block P hr) (canonicalMap (block := block) (P := P) (C := C) hr hD)).asModule,
      Function.Injective j ∧ ∀ v, BinaryFourCanonicalTopScalarEnvelope.Support (j v) := by
  let rho := degreeFourOriginalBinarySocleInflated block P N
  let T := degreeFourOriginalBinaryTargetInflated block P N
  let tau : Representation (ZMod P.p) (preE7NonPairAction w U)
      (BinaryFourCanonicalTopScalarEnvelope.Envelope P.p) :=
    BinaryFourCanonicalTopScalarEnvelope.representation
      (degreeFour_profilePrime_eq_two block P hr)
      (canonicalMap (block := block) (P := P) (C := C) hr hD)
  have hTop : ∃ i : Representation.IntertwiningMap
      (degreeFourOriginalBinaryTopRepresentation block P N) tau,
      Function.Injective i ∧ ∀ v, BinaryFourCanonicalTopScalarEnvelope.Support (i v) :=
    originalBinaryTopEnvelope (block := block) (P := P) (C := C) hr hD N
  obtain ⟨i,hi,hs⟩ := hTop
  let e : (rho.asModule ⧸ T.asSubmodule) ≃ₗ[(ZMod P.p)[preE7NonPairAction w U]]
      (degreeFourOriginalBinaryTopRepresentation block P N).asModule :=
    quotientRepresentationModuleEquiv rho T
  let im : (degreeFourOriginalBinaryTopRepresentation block P N).asModule →ₗ[
      (ZMod P.p)[preE7NonPairAction w U]] tau.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      (degreeFourOriginalBinaryTopRepresentation block P N) tau i
  let j := im.comp e.toLinearMap
  exact ⟨j,hi.comp e.injective,fun v => hs (e v)⟩

end DegreeFourS4OriginalPointChart

namespace DegreeFourA4OriginalPointChart
variable (C : DegreeFourA4OriginalPointChart block)

theorem originalBinaryTopModuleMap
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    ∃ j : ((degreeFourOriginalBinarySocleInflated block P N).asModule ⧸
        (degreeFourOriginalBinaryTargetInflated block P N).asSubmodule) →ₗ[
          (ZMod P.p)[preE7NonPairAction w U]]
      (BinaryFourCanonicalTopScalarEnvelope.representation
        (degreeFour_profilePrime_eq_two block P hr) (canonicalMap (block := block) (P := P) (C := C) hr hD)).asModule,
      Function.Injective j ∧ (∀ v, BinaryFourCanonicalTopScalarEnvelope.Support (j v)) ∧
        (∀ v, (j v).1 2 = 0) := by
  let rho := degreeFourOriginalBinarySocleInflated block P N
  let T := degreeFourOriginalBinaryTargetInflated block P N
  let tau : Representation (ZMod P.p) (preE7NonPairAction w U)
      (BinaryFourCanonicalTopScalarEnvelope.Envelope P.p) :=
    BinaryFourCanonicalTopScalarEnvelope.representation
      (degreeFour_profilePrime_eq_two block P hr)
      (canonicalMap (block := block) (P := P) (C := C) hr hD)
  have hTop : ∃ i : Representation.IntertwiningMap
      (degreeFourOriginalBinaryTopRepresentation block P N) tau,
      Function.Injective i ∧ (∀ v, BinaryFourCanonicalTopScalarEnvelope.Support (i v)) ∧
        (∀ v, (i v).1 2 = 0) :=
    originalBinaryTopEnvelope (block := block) (P := P) (C := C) hr hD N
  obtain ⟨i,hi,hs,hz⟩ := hTop
  let e : (rho.asModule ⧸ T.asSubmodule) ≃ₗ[(ZMod P.p)[preE7NonPairAction w U]]
      (degreeFourOriginalBinaryTopRepresentation block P N).asModule :=
    quotientRepresentationModuleEquiv rho T
  let im : (degreeFourOriginalBinaryTopRepresentation block P N).asModule →ₗ[
      (ZMod P.p)[preE7NonPairAction w U]] tau.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule
      (degreeFourOriginalBinaryTopRepresentation block P N) tau i
  let j := im.comp e.toLinearMap
  exact ⟨j,hi.comp e.injective,(fun v => hs (e v)),fun v => hz (e v)⟩

end DegreeFourA4OriginalPointChart
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
