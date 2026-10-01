import SymmetricSubgroupAsymptotics.Non2PreE7PrimitiveBlockExhaustion
import SymmetricSubgroupAsymptotics.PrimitiveOuterOrderNumerics

/-!
# Exhausting a primitive semisimple outer-log profile

The natural nonaffine primitive profile has a positive number of simple
factors, least proper index `ell`, and quotient order bounded by
`3 log₂ ell`.  The numerical theorems already close every profile with at
least two factors and every one-factor profile with `ell ≥ 30`.  This file
performs that dichotomy and confines the finite primitive certificate to the
exact remaining almost-simple range `ell < 30`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A natural primitive-socle profile together with the bounded certificate
only in the remaining one-factor, least-index-below-thirty case. -/
structure PrimitiveSemisimpleOuterLogCertificateData
    (L : Type) [Group L] (r : ℕ) where
  profile : PrimitiveSemisimpleOuterLogProfile L r
  bounded : profile.factorCount = 1 → profile.leastIndex < 30 →
    LocalSemisimpleCompressionData L r

namespace PrimitiveSemisimpleOuterLogCertificateData

variable {L : Type} [Group L] {r : ℕ}
  (D : PrimitiveSemisimpleOuterLogCertificateData L r)

/-- Every natural outer-log profile, plus only the bounded almost-simple
remainder, gives the exact primitive compression certificate. -/
noncomputable def certificate :
    PrimitiveSemisimpleCompressionCertificate L r := by
  by_cases hmultiple : 2 ≤ D.profile.factorCount
  · exact D.profile.multipleCertificate hmultiple
  · have hone : D.profile.factorCount = 1 := by
      have hpos := D.profile.factorCount_pos
      omega
    by_cases hlarge : 30 ≤ D.profile.leastIndex
    · exact D.profile.largeSimpleCertificate hone hlarge
    · exact .bounded (D.bounded hone (by omega))

end PrimitiveSemisimpleOuterLogCertificateData

namespace Non2UnipotentPrefixFiniteMenu

/-- Final local exhaustion stated in the natural nonaffine primitive data.
All uniform primitive numerics and the actual imprimitive block choice are
discharged by the conversion below. -/
structure PreE7PrimitiveOuterLogExhaustionData where
  small : ∀ w (U : PreE7NonPairActionClass w), w < 5 →
    PreE7RankTailSourceOrYonedaTopData w U
  primitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w) →
    PrimitiveSemisimpleOuterLogCertificateData
        (preE7NonPairAction w U) w ⊕
      PreE7RankTailSourceOrYonedaTopData w U
  imprimitive : ∀ w (U : PreE7NonPairActionClass w), 5 ≤ w →
    (basePoint : Fin w) →
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction w U) basePoint) →
    PrimitiveSemisimpleOuterLogCertificateData block.Component
        (Nat.card block.Fibre) ⊕
      PreE7RankTailSourceOrYonedaTopData w U

namespace PreE7PrimitiveOuterLogExhaustionData

/-- Convert the natural primitive-socle boundary to the already checked
primitive-component exhaustion. -/
noncomputable def toPrimitiveComponentExhaustion
    (D : PreE7PrimitiveOuterLogExhaustionData) :
    PreE7PrimitiveComponentExhaustionData where
  small := D.small
  primitive := by
    intro w U hw hp
    exact match D.primitive w U hw hp with
    | .inl profile => .inl
        { width_lower := hw
          certificate := profile.certificate }
    | .inr source => .inr source
  imprimitive := by
    intro w U hw basePoint block
    exact match D.imprimitive w U hw basePoint block with
    | .inl profile => .inl profile.certificate
    | .inr source => .inr source

/-- T1 from the natural primitive-socle profiles, the bounded
almost-simple certificates below least index thirty, and the already
integrated affine/exceptional/Yoneda sources. -/
theorem T1_of_preE7_primitiveOuterLogExhaustion
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hRDT : MarkedC4.RDTMarkedC4ReductionInput)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (D : PreE7PrimitiveOuterLogExhaustionData)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  D.toPrimitiveComponentExhaustion.T1_of_preE7_primitiveComponentExhaustion
    lit hgen hRDT hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    hOuter hcoarse hFS

end PreE7PrimitiveOuterLogExhaustionData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
