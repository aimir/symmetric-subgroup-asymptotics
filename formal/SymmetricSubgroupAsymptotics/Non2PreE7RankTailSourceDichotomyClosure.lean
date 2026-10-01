import SymmetricSubgroupAsymptotics.Non2PreE7RankTailOwnerOrJointTopClosure
import SymmetricSubgroupAsymptotics.Non2PreE7OrdinaryNumericalInstances

/-!
# Source-level rank-tail dichotomy for T1

The owner proposition used by the numerical recurrence is existential.  This
module exposes its actual constructors: one of the four ordinary template
sources, one of the three correlated rank-tail sources, or the retained
joint top/Yoneda data.  Thus subsequent action-exhaustion proofs construct
mathematical certificates rather than historical labels.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Concrete source of an owner already integrated into the rank-tail
catalogue. -/
inductive PreE7RankTailOwnerSourceData
    (w : ℕ) (U : PreE7NonPairActionClass w) : Type 1 where
  | ordinary (family : PreE7NoPairNoC3EarlierOwnerFamily)
      (source : PreE7OrdinaryNumericalSourceData family w U)
  | b6 (source : PreE7B6SourceData w U)
  | y1 (source : PreE7Y1SourceData w U)
  | sns2 (source : PreE7Sns2SourceData w U)

/-- Every concrete source constructs the literal numerical owner consumed by
the first-owner catalogue. -/
noncomputable def PreE7RankTailOwnerSourceData.toActionOwner
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (S : PreE7RankTailOwnerSourceData w U) :
    PreE7NumericalRankTailActionOwner w U := by
  cases S with
  | ordinary family source =>
      refine ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm family, ?_⟩
      simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
        preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
        (Or.inl (preE7OrdinaryNumericalFamilyAction lit hgen source) :
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction family w U)
  | b6 source =>
      refine ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm .b6, ?_⟩
      simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
        preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
        (Or.inr (Or.inl ⟨rfl, ⟨source⟩⟩) :
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction .b6 w U)
  | y1 source =>
      refine ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm .y1, ?_⟩
      simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
        preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
        (Or.inr (Or.inr (Or.inl ⟨rfl, ⟨source⟩⟩)) :
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction .y1 w U)
  | sns2 source =>
      refine ⟨preE7NoPairNoC3EarlierOwnerEquiv.symm .sns2, ?_⟩
      simpa only [preE7NoPairNoC3EarlierNumericalRankTailFamilyAction,
        preE7NoPairNoC3EarlierOwnerEquiv.apply_symm_apply] using
        (Or.inr (Or.inr (Or.inr ⟨rfl, ⟨source⟩⟩)) :
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction .sns2 w U)

/-- Exact source-facing remaining theorem on one retained action. -/
abbrev PreE7RankTailSourceOrJointTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  PreE7RankTailOwnerSourceData w U ⊕
    PreE7NumericalResidualJointTopCellSourceData w U

/-- Construction-facing version with explicit selected Yoneda-top
families. -/
abbrev PreE7RankTailSourceOrYonedaTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  PreE7RankTailOwnerSourceData w U ⊕
    PreE7NumericalResidualYonedaTopFamilySourceData w U

noncomputable def PreE7RankTailSourceOrJointTopData.toOwnerOrJointTopData
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7RankTailSourceOrJointTopData w U) :
    PreE7NumericalRankTailOwnerOrJointTopData w U :=
  match D with
  | .inl source => .inl (source.toActionOwner lit hgen)
  | .inr cells => .inr cells

noncomputable def PreE7RankTailSourceOrYonedaTopData.toSourceOrJointTopData
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7RankTailSourceOrYonedaTopData w U) :
    PreE7RankTailSourceOrJointTopData w U :=
  match D with
  | .inl source => .inl source
  | .inr cells => .inr cells.toJointTopCellSourceData

/-- T1 from the concrete source-or-joint-top theorem. -/
theorem T1_of_preE7_rankTail_sourceOrJointTop_data
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
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7RankTailSourceOrJointTopData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_numericalRankTail_ownerOrJointTop_data lit
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    (fun w U => (D w U).toOwnerOrJointTopData lit hgen)
    hcoarse hFS hOuter

/-- T1 from the equivalent explicit Yoneda-top-family construction. -/
theorem T1_of_preE7_rankTail_sourceOrYonedaTop_data
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
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7RankTailSourceOrYonedaTopData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_rankTail_sourceOrJointTop_data lit hgen
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    (fun w U => (D w U).toSourceOrJointTopData)
    hcoarse hFS hOuter

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
