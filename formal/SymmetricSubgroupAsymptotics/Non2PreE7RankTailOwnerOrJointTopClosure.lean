import SymmetricSubgroupAsymptotics.Non2PreE7RankTailNumericalClosure
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2OwnerOrJointTopClosure

/-!
# T1 from the rank-tail owner or joint-capacity dichotomy

B6 and Y1 are now discharged alongside the ordinary numerical and SNS2
owners.  An action which remains terminal is sent unchanged to the proved
annihilator-aware joint top/Yoneda incidence row.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Every ordinary-or-SNS2 owner belongs to the enlarged rank-tail
catalogue. -/
theorem preE7NoPairNoC3EarlierFamilyPredicate_sns2_le_rankTail
    (n : ℕ) (k : Fin preE7NoPairNoC3EarlierOwnerCount)
    (H : Subgroup (Equiv.Perm (Fin n))) :
    preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction n k H →
      preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction n k H := by
  rintro ⟨W⟩
  refine ⟨{ W with applies := ?_ }⟩
  rcases W.applies with hordinary | hsns2
  · exact Or.inl hordinary
  · exact Or.inr (Or.inr (Or.inr hsns2))

/-- A terminal state after adding B6 and Y1 was already terminal for the
ordinary-plus-SNS2 catalogue. -/
theorem preE7NumericalRankTail_terminal_implies_sns2_terminal
    (w b : ℕ) (U : PreE7NonPairActionClass w)
    (H : Subgroup (preE7NonPairAction w U × Equiv.Perm (Fin b))) :
    preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b H →
      preE7NoPairNoC3CertifiedFirstOwnerPredicate
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
        (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b H := by
  rintro ⟨⟨howner, hnoC3⟩, _hselected⟩
  rcases howner with ⟨hordinary, hfirst⟩
  let K : Subgroup (Equiv.Perm (Fin (w + b))) :=
    relabelSubgroup finSumFinEquiv
      (H.map (fusionOrbitAction (preE7NonPairAction w U)))
  have hunownedRankTail : ∀ k : Fin preE7NoPairNoC3EarlierOwnerCount,
      ¬ preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction (w + b) k K :=
    (firstOwned_ownerOrResidual_last_iff
      (preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalRankTailFamilyAction) K).mp hfirst
  have hunownedSns2 : ∀ k : Fin preE7NoPairNoC3EarlierOwnerCount,
      ¬ preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction (w + b) k K := by
    intro k hk
    exact hunownedRankTail k
      (preE7NoPairNoC3EarlierFamilyPredicate_sns2_le_rankTail
        (w + b) k K hk)
  have hfirstSns2 : FirstOwned
      (ownerOrResidualEligible
        (preE7NoPairNoC3EarlierFamilyPredicate
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction) (w + b))
      (Fin.last preE7NoPairNoC3EarlierOwnerCount) K :=
    (firstOwned_ownerOrResidual_last_iff
      (preE7NoPairNoC3EarlierFamilyPredicate
        preE7NoPairNoC3EarlierNumericalSns2FamilyAction) K).mpr
      hunownedSns2
  refine ⟨⟨⟨hordinary, ?_⟩, hnoC3⟩,
    preE7NoPairNoC3SelectedActionEligible_last _ U⟩
  simpa only [K] using hfirstSns2

/-- An actual enlarged-catalogue owner of one retained action. -/
abbrev PreE7NumericalRankTailActionOwner
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  {k : Fin preE7NoPairNoC3EarlierOwnerCount //
    preE7NoPairNoC3EarlierNumericalRankTailFamilyAction
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U}

/-- Exact remaining alternative: an enlarged-catalogue owner, or the joint
annihilator-aware cell data. -/
abbrev PreE7NumericalRankTailOwnerOrJointTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  PreE7NumericalRankTailActionOwner w U ⊕
    PreE7NumericalResidualJointTopCellSourceData w U

/-- Construction-facing version using explicit Yoneda-top families. -/
abbrev PreE7NumericalRankTailOwnerOrYonedaTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  PreE7NumericalRankTailActionOwner w U ⊕
    PreE7NumericalResidualYonedaTopFamilySourceData w U

/-- An owned action cannot survive in the new terminal branch. -/
theorem preE7NumericalRankTail_terminalAccepted_isEmpty_of_actionOwner
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (owner : PreE7NumericalRankTailActionOwner w U) (b : ℕ) :
    IsEmpty {H : Subgroup
        (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
      FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) H} := by
  refine ⟨?_⟩
  rintro ⟨H, hfull, hterminal⟩
  obtain ⟨k, hk⟩ := owner
  let G : Subgroup (Equiv.Perm (Fin (w + b))) :=
    relabelSubgroup finSumFinEquiv
      (H.map (fusionOrbitAction (preE7NonPairAction w U)))
  have howned : preE7NoPairNoC3EarlierFamilyPredicate
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction (w + b) k G := by
    have h := preE7EarlierFamilyPredicate_of_fullDisplayedAction
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction U hk H hfull
    simpa only [Equiv.symm_apply_apply, G] using h
  have hfirst : FirstOwned
      (ownerOrResidualEligible
        (preE7NoPairNoC3EarlierFamilyPredicate
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction) (w + b))
      (Fin.last preE7NoPairNoC3EarlierOwnerCount) G :=
    hterminal.1.1.2
  have hunowned := (firstOwned_ownerOrResidual_last_iff
    (preE7NoPairNoC3EarlierFamilyPredicate
      preE7NoPairNoC3EarlierNumericalRankTailFamilyAction) G).mp hfirst
  exact hunowned k howned

/-- An actually owned action receives the zero terminal row. -/
noncomputable def PreE7NumericalRankTailResidualChoice.emptyOfActionOwner
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (owner : PreE7NumericalRankTailActionOwner w U) :
    PreE7NumericalRankTailResidualChoice w U where
  D := fun _ => 0
  v := preE7EmptyCellDegree w
  eta := 0
  delta := preE7EmptyCellDelta w
  cutoff := preE7EmptyCellCutoff w
  alpha := preE7EmptyCellAlpha w
  theta := 0
  alpha_eq := by simp [preE7EmptyCellAlpha]
  D_nonneg := fun _ => le_rfl
  parameters := preE7EmptyCell_entryParameters
    (preE7NonPairAction_width_three_le U)
  main_total_bound := fun _ => by positivity
  local_bound := by
    intro b
    letI : IsEmpty {H : Subgroup
        (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
      FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) H} :=
      preE7NumericalRankTail_terminalAccepted_isEmpty_of_actionOwner
        U owner b
    let F := FusionOrbitFamily (preE7NonPairAction w U)
      (FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b))
    haveI : IsEmpty F := by
      refine ⟨fun K => ?_⟩
      obtain ⟨_, ⟨⟨_, ⟨_, ⟨⟨M, hM⟩, rfl⟩⟩⟩, rfl⟩⟩ := K
      exact isEmptyElim
        (α := {H : Subgroup
            (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
          FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
            (preE7NoPairNoC3CertifiedFirstOwnerPredicate
              preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
              (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) H})
        ⟨M, hM⟩
    have hcard : Nat.card F = 0 := Nat.card_of_isEmpty
    change (Nat.card F : ℝ) / exactBenchmark (b + w) ≤ _
    rw [hcard]
    simp [growingQuotientHotKernel, fusionWidthColdKernel]

/-- The old joint cells apply unchanged because the enlarged terminal
predicate only removes sources. -/
noncomputable def
    PreE7NumericalRankTailResidualChoice.ofNumericalResidualJointTopCells
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalResidualJointTopCellSourceData w U) :
    PreE7NumericalRankTailResidualChoice w U := by
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
          preE7NoPairNoC3EarlierNumericalRankTailFamilyAction w
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
                    (fun H hH =>
                      preE7NumericalSns2_terminal_implies_numerical_terminal
                        w b U H
                        (preE7NumericalRankTail_terminal_implies_sns2_terminal
                          w b U H hH)) N J).trans (by
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

/-- Select the zero row for an owner and the joint-incidence row otherwise. -/
noncomputable def PreE7NumericalRankTailOwnerOrJointTopData.residualChoice
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalRankTailOwnerOrJointTopData w U) :
    PreE7NumericalRankTailResidualChoice w U :=
  match D with
  | .inl owner => .emptyOfActionOwner U owner
  | .inr cells => .ofNumericalResidualJointTopCells cells

noncomputable def preE7NumericalRankTail_ownerOrJointTopResidualChoices
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalRankTailOwnerOrJointTopData w U) :
    ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalRankTailResidualChoice w U :=
  fun w U => (D w U).residualChoice

noncomputable def
    PreE7NumericalRankTailOwnerOrYonedaTopData.toOwnerOrJointTopData
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalRankTailOwnerOrYonedaTopData w U) :
    PreE7NumericalRankTailOwnerOrJointTopData w U :=
  match D with
  | .inl owner => .inl owner
  | .inr cells => .inr cells.toJointTopCellSourceData

/-- T1 now requires the terminal dichotomy only after ordinary, B6, Y1,
and SNS2 ownership have all been tested. -/
theorem T1_of_preE7_numericalRankTail_ownerOrJointTop_data
    (lit : PreE7CharacterLiterature)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalRankTailOwnerOrJointTopData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_numericalRankTail_residual lit
    (preE7NumericalRankTail_ownerOrJointTopResidualChoices D)
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM hcoarse
    hFS hOuter

/-- Equivalent T1 boundary from explicit Yoneda-top-family data. -/
theorem T1_of_preE7_numericalRankTail_ownerOrYonedaTop_data
    (lit : PreE7CharacterLiterature)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalRankTailOwnerOrYonedaTopData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_numericalRankTail_ownerOrJointTop_data lit
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    (fun w U => (D w U).toOwnerOrJointTopData)
    hcoarse hFS hOuter

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
