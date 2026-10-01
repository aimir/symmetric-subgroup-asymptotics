import SymmetricSubgroupAsymptotics.Non2PreE7Sns2NumericalClosure
import SymmetricSubgroupAsymptotics.T1NumericalJointTopClosure

/-!
# Restrict numerical joint-top terminal cells after adding SNS2

Adding the globally correlated SNS2 owner only shrinks the terminal branch.
The previously retained annihilator-aware joint top/Yoneda cells therefore
apply unchanged, with their original action weights and numerical parameters.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Every numerical earlier owner is also an owner of the enlarged
numerical-plus-SNS2 catalogue. -/
theorem preE7NoPairNoC3EarlierFamilyPredicate_numerical_le_sns2
    (n : ℕ) (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    (H : Subgroup (Equiv.Perm (Fin n))) :
    preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalFamilyAction n k H →
      preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction n k H := by
  rintro ⟨W⟩
  refine ⟨{ W with applies := Or.inl W.applies }⟩

/-- A terminal state for the enlarged catalogue was already terminal for the
numerical pointwise catalogue. -/
theorem preE7NumericalSns2_terminal_implies_numerical_terminal
    (w b : ℕ) (U : PreE7NonPairActionClass w)
    (H : Subgroup (preE7NonPairAction w U × Equiv.Perm (Fin b))) :
    preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b H →
      preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierNumericalFamilyAction w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b H := by
  rintro ⟨⟨howner, hnoC3⟩, _hselected⟩
  rcases howner with ⟨hordinary, hfirst⟩
  let K : Subgroup (Equiv.Perm (Fin (w + b))) :=
    relabelSubgroup finSumFinEquiv
      (H.map (fusionOrbitAction (preE7NonPairAction w U)))
  have hunownedSns2 : ∀ k : Fin preE7NoPairNoC3EarlierOwnerCount,
      ¬ preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction (w + b) k K :=
    (firstOwned_ownerOrResidual_last_iff
      (preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction) K).mp hfirst
  have hunownedNumerical : ∀ k : Fin preE7NoPairNoC3EarlierOwnerCount,
      ¬ preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalFamilyAction (w + b) k K := by
    intro k hk
    exact hunownedSns2 k
      (preE7NoPairNoC3EarlierFamilyPredicate_numerical_le_sns2
        (w + b) k K hk)
  have hfirstNumerical : FirstOwned
      (ownerOrResidualEligible
        (preE7NoPairNoC3EarlierFamilyPredicate
          preE7NoPairNoC3EarlierNumericalFamilyAction) (w + b))
      (Fin.last preE7NoPairNoC3EarlierOwnerCount) K :=
    (firstOwned_ownerOrResidual_last_iff
      (preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalFamilyAction) K).mpr
      hunownedNumerical
  refine ⟨⟨⟨hordinary, ?_⟩, hnoC3⟩,
    preE7NoPairNoC3SelectedActionEligible_last _ U⟩
  simpa only [K] using hfirstNumerical

/-- Existing numerical joint top/Yoneda cells give the terminal local row of
the enlarged numerical-plus-SNS2 catalogue. -/
noncomputable def
    PreE7NumericalSns2ResidualChoice.ofNumericalResidualJointTopCells
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalResidualJointTopCellSourceData w U) :
    PreE7NumericalSns2ResidualChoice w U := by
  let Dmain : ℕ → ℝ := fun b =>
    fusionAxisEnvelopeTotal (preE7NonPairAction w U) (D.C b)
  exact
    { D := Dmain
      v := D.v
      eta := D.eta
      delta := D.delta
      cutoff := D.cutoff
      alpha := D.alpha
      theta := D.theta
      alpha_eq := D.alpha_eq
      D_nonneg := fun b =>
        fusionAxisEnvelopeTotal_nonneg _ _ (D.coefficient_nonneg b)
      parameters := D.parameters
      main_total_bound := D.coefficient_total_bound
      local_bound := by
        intro b
        let P := preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b
        have hsource (J : Subgroup (Equiv.Perm (Fin b))) :
            fusionCompleteSourceSum (preE7NonPairAction w U) P J ≤
              (Dmain b * (2 : ℝ) ^ (D.eta * b)) *
                  completeQuotientWeight (R := D.R) J +
                0 * (2 : ℝ) ^ (D.theta * b) := by
          calc
            _ ≤ fusionAxisEnvelopeTotal (preE7NonPairAction w U) (D.C b) *
                ((2 : ℝ) ^ (D.eta * b) *
                  completeQuotientWeight (R := D.R) J) :=
              fusionCompleteSourceSum_le_axisEnvelopeTotal
                (preE7NonPairAction w U) P (D.C b)
                (fun J => (2 : ℝ) ^ (D.eta * b) *
                  completeQuotientWeight (R := D.R) J)
                (fun N J => by
                  exact (fusionSurvivingEpiCount_mono
                    (preE7NumericalSns2_terminal_implies_numerical_terminal
                      w b U) N J).trans (by
                        simpa only [mul_assoc] using D.axis_envelope b N J)) J
            _ = _ := by unfold Dmain; ring
        have h := fusionPhysical_growingQuotient_additiveTail_kernel_bound
          (preE7NonPairAction w U) P
          (preE7NoPairNoC3CertifiedFirstOwnerPredicate_natural _ w
            (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b)
          D.action D.action_injective (Dmain b) 0 D.eta D.theta D.delta
          D.cutoff
          (fusionAxisEnvelopeTotal_nonneg _ _ (D.coefficient_nonneg b))
          le_rfl hsource
        simpa [P, Dmain, D.alpha_eq, fusionWidthColdKernel,
          ordinarySubgroupRatio] using h }

/-- Assemble the restricted terminal choices for every literal action. -/
noncomputable def preE7NumericalSns2_residualChoices
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalResidualJointTopCellSourceData w U) :
    ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalSns2ResidualChoice w U :=
  fun _ _ =>
    PreE7NumericalSns2ResidualChoice.ofNumericalResidualJointTopCells (D _ _)

/-- Joint terminal cells, the numerical ordinary catalogue, and SNS2 close
T1 through one disjoint physical recurrence. -/
theorem T1_of_preE7_numericalSns2_jointTopCell_data
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalResidualJointTopCellSourceData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_numericalSns2_residual
    (preE7NumericalSns2_residualChoices D)
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM hcoarse
    hFS hOuter

/-- The annihilator-aware Yoneda-top-family presentation gives the same
closed T1 boundary.  The retained flag and its Yoneda fibre are still charged
jointly before the complete quotient moment is applied. -/
theorem T1_of_preE7_numericalSns2_yonedaTopFamily_data
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalResidualYonedaTopFamilySourceData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_numericalSns2_jointTopCell_data
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    (fun w U => (D w U).toJointTopCellSourceData)
    hcoarse hFS hOuter

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
