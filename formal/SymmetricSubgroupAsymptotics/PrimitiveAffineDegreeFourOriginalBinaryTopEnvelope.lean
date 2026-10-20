import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinaryTopCanonicalImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalCanonicalCoreAction
import SymmetricSubgroupAsymptotics.BinaryFourCanonicalTopScalarEnvelope

/-! Complete ORIGINAL top quotient envelope maps. Every original N is
transported to its own canonical normal image before the zero/nonzero case
split. The original quotient module, conjugation and scalar are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]
local instance originalBinaryTopEnvelopePrime : Fact P.p.Prime := ⟨P.p_prime⟩

namespace DegreeFourS4OriginalPointChart
variable (C : DegreeFourS4OriginalPointChart block)

theorem originalBinaryTopEnvelope
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    ∃ i : (degreeFourOriginalBinaryTopRepresentation block P N).IntertwiningMap
        (BinaryFourCanonicalTopScalarEnvelope.representation
          (degreeFour_profilePrime_eq_two block P hr) (canonicalMap (block := block) (P := P) (C := C) hr hD)),
      Function.Injective i ∧ ∀ v, BinaryFourCanonicalTopScalarEnvelope.Support (i v) := by
  let e := (groupEquiv (block := block) (P := P) (C := C) hr hD)
  let S := DegreeFourFullBinarySocleChart block P N
  letI : FiniteDimensional (ZMod P.p) S.quotientRepresentation := S.finiteDimensional
  letI : FiniteDimensional (ZMod P.p) (DegreeFourOriginalBinaryTopVector block P N) := inferInstance
  exact BinaryFourCanonicalTopScalarEnvelope.s4_top_intertwiner
    (degreeFour_profilePrime_eq_two block P hr)
    (degreeFourCanonicalNormalImage block P e N)
    (degreeFourCanonicalOriginalMap block P e)
    (degreeFourOriginalBinaryTopRepresentation block P N)
    (degreeFourOriginalBinaryTopCanonicalInjection block P e N)
    (degreeFourOriginalBinaryTopCanonicalInjection_injective block P e N)
    inferInstance
    (degreeFourOriginalBinaryTopCanonicalInjection_range_isPGroup block P e hr N)
    (degreeFourOriginalBinaryTopCanonicalInjection_conjugate block P e N)

end DegreeFourS4OriginalPointChart

namespace DegreeFourA4OriginalPointChart
variable (C : DegreeFourA4OriginalPointChart block)

theorem originalBinaryTopEnvelope
    (hr : Nat.card block.Fibre = 4) (hD : degreeFourTernaryCore block P = ⊥)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    ∃ i : (degreeFourOriginalBinaryTopRepresentation block P N).IntertwiningMap
        (BinaryFourCanonicalTopScalarEnvelope.representation
          (degreeFour_profilePrime_eq_two block P hr) (canonicalMap (block := block) (P := P) (C := C) hr hD)),
      Function.Injective i ∧ (∀ v, BinaryFourCanonicalTopScalarEnvelope.Support (i v)) ∧
        (∀ v, (i v).1 2 = 0) := by
  let e := (groupEquiv (block := block) (P := P) (C := C) hr hD)
  exact BinaryFourCanonicalTopScalarEnvelope.a4_top_intertwiner
    (degreeFour_profilePrime_eq_two block P hr)
    (degreeFourCanonicalNormalImage block P e N)
    (degreeFourCanonicalOriginalMap block P e)
    (degreeFourOriginalBinaryTopRepresentation block P N)
    (degreeFourOriginalBinaryTopCanonicalInjection block P e N)
    (degreeFourOriginalBinaryTopCanonicalInjection_injective block P e N)
    inferInstance
    (degreeFourOriginalBinaryTopCanonicalInjection_range_isPGroup block P e hr N)
    (degreeFourOriginalBinaryTopCanonicalInjection_conjugate block P e N)

end DegreeFourA4OriginalPointChart
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
