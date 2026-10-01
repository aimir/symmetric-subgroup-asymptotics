import SymmetricSubgroupAsymptotics.Non2PreE7Sns2ExhaustionClosure
import SymmetricSubgroupAsymptotics.Non2PreE7Sns2ResidualJointTop

/-!
# T1 from the exact earlier-owner or joint-capacity dichotomy

The terminal theorem does not require joint cells on an action which is
already accepted by one of the numerical earlier families.  Conversely,
action-level owner exhaustion is stronger than the historical result: the
post-D0407 residual is precisely where the joint retained-cell theorem is
used.

This file records the exact dichotomy.  For every literal retained action,
one supplies either an actual earlier-owner certificate or the complete
annihilator-aware joint top/Yoneda data.  The former makes the terminal cell
empty; the latter is passed unchanged to the proved weighted-incidence row.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- An actual numerical earlier owner of one literal retained action. -/
abbrev PreE7NumericalSns2ActionOwner
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  {k : Fin preE7NoPairNoC3EarlierOwnerCount //
    preE7NoPairNoC3EarlierNumericalSns2FamilyAction
      (preE7NoPairNoC3EarlierOwnerEquiv k) w U}

/-- The exact terminal alternative on one retained action: an earlier owner
already accepts it, or its reversible carrier carries the joint cells used by
the numerical incidence theorem. -/
abbrev PreE7NumericalSns2OwnerOrJointTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  PreE7NumericalSns2ActionOwner w U ⊕
    PreE7NumericalResidualJointTopCellSourceData w U

/-- Equivalent construction-facing form in which the residual branch is a
finite family of actual annihilator-aware Yoneda tops. -/
abbrev PreE7NumericalSns2OwnerOrYonedaTopData
    (w : ℕ) (U : PreE7NonPairActionClass w) :=
  PreE7NumericalSns2ActionOwner w U ⊕
    PreE7NumericalResidualYonedaTopFamilySourceData w U

/-- One accepted action cannot occur in the appended terminal branch.  This
is the local form of action exhaustion and uses only the supplied owner. -/
theorem preE7NumericalSns2_terminalAccepted_isEmpty_of_actionOwner
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (owner : PreE7NumericalSns2ActionOwner w U) (b : ℕ) :
    IsEmpty {H : Subgroup
        (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
      FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) H} := by
  refine ⟨?_⟩
  rintro ⟨H, hfull, hterminal⟩
  obtain ⟨k, hk⟩ := owner
  let G : Subgroup (Equiv.Perm (Fin (w + b))) :=
    relabelSubgroup finSumFinEquiv
      (H.map (fusionOrbitAction (preE7NonPairAction w U)))
  have howned : preE7NoPairNoC3EarlierFamilyPredicate
      preE7NoPairNoC3EarlierNumericalSns2FamilyAction (w + b) k G := by
    have h := preE7EarlierFamilyPredicate_of_fullDisplayedAction
      preE7NoPairNoC3EarlierNumericalSns2FamilyAction U hk H hfull
    simpa only [Equiv.symm_apply_apply, G] using h
  have hfirst : FirstOwned
      (ownerOrResidualEligible
        (preE7NoPairNoC3EarlierFamilyPredicate
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction) (w + b))
      (Fin.last preE7NoPairNoC3EarlierOwnerCount) G :=
    hterminal.1.1.2
  have hunowned := (firstOwned_ownerOrResidual_last_iff
    (preE7NoPairNoC3EarlierFamilyPredicate
      preE7NoPairNoC3EarlierNumericalSns2FamilyAction) G).mp hfirst
  exact hunowned k howned

/-- An actually owned action receives the harmless zero terminal row. -/
noncomputable def PreE7NumericalSns2ResidualChoice.emptyOfActionOwner
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (owner : PreE7NumericalSns2ActionOwner w U) :
    PreE7NumericalSns2ResidualChoice w U where
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
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) H} :=
      preE7NumericalSns2_terminalAccepted_isEmpty_of_actionOwner U owner b
    let F := FusionOrbitFamily (preE7NonPairAction w U)
      (FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b))
    haveI : IsEmpty F := by
      refine ⟨fun K => ?_⟩
      obtain ⟨_, ⟨⟨_, ⟨_, ⟨⟨M, hM⟩, rfl⟩⟩⟩, rfl⟩⟩ := K
      exact isEmptyElim
        (α := {H : Subgroup
            (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
          FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
            (preE7NoPairNoC3CertifiedFirstOwnerPredicate
              preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
              (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) H})
        ⟨M, hM⟩
    have hcard : Nat.card F = 0 := Nat.card_of_isEmpty
    change (Nat.card F : ℝ) / exactBenchmark (b + w) ≤ _
    rw [hcard]
    simp [growingQuotientHotKernel, fusionWidthColdKernel]

/-- Select the zero row on an owned action and the proved joint-incidence row
on a genuinely residual action. -/
noncomputable def PreE7NumericalSns2OwnerOrJointTopData.residualChoice
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalSns2OwnerOrJointTopData w U) :
    PreE7NumericalSns2ResidualChoice w U :=
  match D with
  | .inl owner => .emptyOfActionOwner U owner
  | .inr cells => .ofNumericalResidualJointTopCells cells

/-- Assemble the exact dichotomy over all retained actions. -/
noncomputable def preE7NumericalSns2_ownerOrJointTopResidualChoices
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalSns2OwnerOrJointTopData w U) :
    ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalSns2ResidualChoice w U :=
  fun w U => (D w U).residualChoice

/-- Forget the presentation of a residual cell as a selected Yoneda-top
family while retaining the same joint capacity. -/
noncomputable def
    PreE7NumericalSns2OwnerOrYonedaTopData.toOwnerOrJointTopData
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (D : PreE7NumericalSns2OwnerOrYonedaTopData w U) :
    PreE7NumericalSns2OwnerOrJointTopData w U :=
  match D with
  | .inl owner => .inl owner
  | .inr cells => .inr cells.toJointTopCellSourceData

/-- Publication-facing T1 boundary for the valid terminal dichotomy.  The
remaining structural theorem must construct `D`; it may not replace the
joint-cell branch by a bare historical label. -/
theorem T1_of_preE7_numericalSns2_ownerOrJointTop_data
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalSns2OwnerOrJointTopData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_numericalSns2_residual
    (preE7NumericalSns2_ownerOrJointTopResidualChoices D)
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM hcoarse
    hFS hOuter

/-- The construction-facing Yoneda-top-family dichotomy proves the same T1
boundary. -/
theorem T1_of_preE7_numericalSns2_ownerOrYonedaTop_data
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (D : ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalSns2OwnerOrYonedaTopData w U)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_numericalSns2_ownerOrJointTop_data
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM
    (fun w U => (D w U).toOwnerOrJointTopData)
    hcoarse hFS hOuter

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
