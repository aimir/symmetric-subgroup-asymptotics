import SymmetricSubgroupAsymptotics.Non2PreE7Sns2NumericalClosure
import SymmetricSubgroupAsymptotics.FusionAcceptedOrbitChartAt

/-!
# T1 from exhaustive numerical action certificates

The final residual cell is needed only for a literal pre-`E7` action which
belongs to none of the numerically certified ordinary families and does not
carry an SNS2 certificate.  If the action catalogue is exhaustive, a full
displayed action is itself an orbit carrying an earlier-family certificate.
This contradicts first ownership by the appended terminal branch.

Thus catalogue exhaustion makes every terminal orbit family empty.  The
empty-cell parameter package then closes the numerical/SNS2 recurrence
without constructing artificial Yoneda cells for already owned actions.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- Every retained pre-`E7` action has a numerically complete ordinary or
SNS2 certificate.  This is the exact action-level exhaustion statement left
after the five family templates have been instantiated. -/
def PreE7NumericalSns2ActionExhaustion : Prop :=
  ∀ w (U : PreE7NonPairActionClass w),
    ∃ k : Fin preE7NoPairNoC3EarlierOwnerCount,
      preE7NoPairNoC3EarlierNumericalSns2FamilyAction
        (preE7NoPairNoC3EarlierOwnerEquiv k) w U

/-- A full displayed original action gives a literal orbit certificate for
that same action and family in the complete physical subgroup. -/
theorem preE7EarlierFamilyPredicate_of_fullDisplayedAction
    (FamilyAction : PreE7NoPairNoC3EarlierOwnerFamily →
      ∀ w, PreE7NonPairActionClass w → Prop)
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w b : ℕ} (U : PreE7NonPairActionClass w)
    (hfamily : FamilyAction family w U)
    (H : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)))
    (hfull : H.map (MonoidHom.fst
      (preE7NonPairAction w U) (Equiv.Perm (Fin b))) = ⊤) :
    preE7NoPairNoC3EarlierFamilyPredicate FamilyAction (w + b)
      (preE7NoPairNoC3EarlierOwnerEquiv.symm family)
      (relabelSubgroup finSumFinEquiv
        (H.map (fusionOrbitAction (preE7NonPairAction w U)))) := by
  have hw : 3 ≤ w := preE7NonPairAction_width_three_le U
  let x : Fin w := ⟨0, by omega⟩
  let G : Subgroup (Equiv.Perm (Fin (w + b))) :=
    relabelSubgroup finSumFinEquiv
      (H.map (fusionOrbitAction (preE7NonPairAction w U)))
  let o : OrbitProfileFromOrbits.Orbit G :=
    Quotient.mk'' (finSumFinEquiv (Sum.inl x))
  have htrans : ∀ y z : Fin w, ∃ u : preE7NonPairAction w U,
      (u : Equiv.Perm (Fin w)) y = z := by
    intro y z
    letI : MulAction.IsPretransitive U.1.1.representative (Fin w) :=
      Non2TransitiveActionClass.representative_pretransitive U.1.1
    change ∃ u : U.1.1.representative,
      (u : Equiv.Perm (Fin w)) y = z
    exact MulAction.exists_smul_eq U.1.1.representative y z
  obtain ⟨e, he⟩ := fusionAcceptedOrbit_physical_orbit_chart_at
    (preE7NonPairAction w U) htrans finSumFinEquiv H hfull x
  refine ⟨{
    width := w
    action := U
    applies := by simpa using hfamily
    width_three := hw
    orbit := o
    chart := e
    action_eq := ?_ }⟩
  simpa only [G, o] using he

/-- Under action-level exhaustion, no full local source can survive in the
appended terminal branch. -/
theorem preE7NumericalSns2_terminalAccepted_isEmpty
    (hExhaustive : PreE7NumericalSns2ActionExhaustion)
    (w b : ℕ) (U : PreE7NonPairActionClass w) :
    IsEmpty {H : Subgroup
        (preE7NonPairAction w U × Equiv.Perm (Fin b)) //
      FusionAcceptedOrbitPredicate (preE7NonPairAction w U)
        (preE7NoPairNoC3CertifiedFirstOwnerPredicate
          preE7NoPairNoC3EarlierNumericalSns2FamilyAction w
          (Fin.last preE7NoPairNoC3EarlierOwnerCount, U) b) H} := by
  refine ⟨?_⟩
  rintro ⟨H, hfull, hterminal⟩
  obtain ⟨k, hk⟩ := hExhaustive w U
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
      (Fin.last preE7NoPairNoC3EarlierOwnerCount) G := by
    exact hterminal.1.1.2
  have hunowned := (firstOwned_ownerOrResidual_last_iff
    (preE7NoPairNoC3EarlierFamilyPredicate
      preE7NoPairNoC3EarlierNumericalSns2FamilyAction) G).mp hfirst
  exact hunowned k howned

/-- Catalogue exhaustion supplies the harmless zero terminal row. -/
noncomputable def PreE7NumericalSns2ResidualChoice.emptyOfActionExhaustion
    (hExhaustive : PreE7NumericalSns2ActionExhaustion)
    (w : ℕ) (U : PreE7NonPairActionClass w) :
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
      preE7NumericalSns2_terminalAccepted_isEmpty hExhaustive w b U
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

/-- Assemble the empty terminal choices after exhaustive family
instantiation. -/
noncomputable def preE7NumericalSns2_emptyResidualChoices
    (hExhaustive : PreE7NumericalSns2ActionExhaustion) :
    ∀ w (U : PreE7NonPairActionClass w),
      PreE7NumericalSns2ResidualChoice w U :=
  fun w U =>
    PreE7NumericalSns2ResidualChoice.emptyOfActionExhaustion
      hExhaustive w U

/-- Publication-facing T1 boundary after the five family templates cover
every retained pre-`E7` action. -/
theorem T1_of_preE7_numericalSns2_actionExhaustion
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (hKP : KovacsPraegerAbelianizationBound)
    (hLMM : LucchiniMenegazzoMorigiTransitiveCountInput)
    (hExhaustive : PreE7NumericalSns2ActionExhaustion)
    (hcoarse : FusionCoarseEstimate (fun n => (subgroupCount n : ℝ)))
    (hFS : FusariSpigaBinaryNormalSubgroupInput)
    (hOuter : SemisimpleOuterFactorPermutationBound) : T1 :=
  T1_of_preE7_numericalSns2_residual
    (preE7NumericalSns2_emptyResidualChoices hExhaustive)
    hTracey hExceptional hChief hWeight hPrimitive h18 hKP hLMM hcoarse
    hFS hOuter

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
