import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleCompression

/-!
# T1 from semisimple compression or the retained source dichotomy

This is the structural frontier after complete semisimple compression.  On
each literal pre-`E7` non-pair action, the exhaustion proof may provide the
compression datum itself.  Only actions without that datum must enter an
already integrated owner source or the annihilator-aware Yoneda-top lane.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Exact post-compression structural obligation on one retained action. -/
abbrev PreE7CompressionOrSourceOrYonedaTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  PreE7SemisimpleCompressionData w U ⊕
    PreE7RankTailSourceOrYonedaTopData w U

/-- A compression witness becomes the concrete `.comp` source; every other
source is retained literally. -/
noncomputable def
    PreE7CompressionOrSourceOrYonedaTopData.toSourceOrYonedaTopData
    (hOuter : SemisimpleOuterFactorPermutationBound)
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7CompressionOrSourceOrYonedaTopData w U) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  match D with
  | .inl compression => .inl (compression.toRankTailOwnerSource hOuter)
  | .inr source => source

/-- T1 from the post-compression source exhaustion theorem. -/
theorem T1_of_preE7_semisimpleCompression_or_sourceOrYonedaTop_data
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hOuter : SemisimpleOuterFactorPermutationBound)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7CompressionOrSourceOrYonedaTopData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput) : T1 :=
  T1_of_preE7_rankTail_sourceOrYonedaTop_data lit hgen
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    (fun w U => (D w U).toSourceOrYonedaTopData hOuter)
    hcoarse hFS hOuter

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
