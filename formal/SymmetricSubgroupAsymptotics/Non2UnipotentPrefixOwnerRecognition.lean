import SymmetricSubgroupAsymptotics.Non2OriginalFusionFaithfulCover
import SymmetricSubgroupAsymptotics.Non2OriginalFusionOwnerBridge
import SymmetricSubgroupAsymptotics.Non2UnipotentPrefixFiniteMenu

/-!
# Recognition by the earlier unipotent-prefix owner

Every axis in the fixed pair menu has the arbitrary-normal-axis nonbinary
payload.  Its selected retained cut already satisfies the strict numerical
inequality used by the historical unipotent-prefix owner.  This file packages
that implication and isolates the one application-specific recognition
statement: the earlier owner must accept every Goursat reconstruction carrying
such a certified cut.  Under that statement the residual axis pays zero; no
second nonbinary recurrence is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The numerical fixed-cut condition recognized by the earlier
unipotent-prefix owner. -/
def FixedCutUPCertified {B : Type} [Group B]
    (M : Rep (ZMod 2) B) (s : ℕ) : Prop :=
  ∃ C : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants},
    2 * (Module.finrank (ZMod 2) C.1 : ℝ) +
        4 * OriginalCentralCutFusion.capacity M C < s

namespace Non2OriginalFusionCertificate

/-- The checked `47s/48` capacity inequality is strictly inside the UP
threshold at every positive pair count. -/
theorem fixedCutUPCertified
    {B : Type} [Group B] {M : Rep (ZMod 2) B} {s : ℕ}
    (C : Non2OriginalFusionCertificate M s) (hs : 0 < s) :
    FixedCutUPCertified M s := by
  refine ⟨C.cut, ?_⟩
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  linarith [C.cost_le]

end Non2OriginalFusionCertificate

namespace Non2UnipotentPrefixFiniteMenu

/-- The complete arbitrary-axis payload on a fixed UP-menu action. -/
noncomputable def axisPayload
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (i : ActionIndex)
    (N : {N : Subgroup (sourceAction i) // N.Normal}) :
    Non2OriginalFusionAxisPayload (pairCount i) (sourceAction i) N :=
  Classical.choice
    ((chosenFrame i).exists_non2OriginalFusionAxisPayload_of_arbitraryPairAxis
      N hTracey hExceptional (chosenTop_not_isPGroup i)
      ⟨0, PairCountLabel.pairCount_pos i.1⟩
      (PairCountLabel.pairCount_ge_24 i.1)
      (PairCountLabel.pairCount_even i.1))

theorem axisPayload_fixedCutUPCertified
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (i : ActionIndex)
    (N : {N : Subgroup (sourceAction i) // N.Normal}) :
    FixedCutUPCertified (axisPayload hTracey hExceptional i N).M
      (pairCount i) :=
  (axisPayload hTracey hExceptional i N).certificate.fixedCutUPCertified
    (PairCountLabel.pairCount_pos i.1)

/-- Physical earlier ownership of one local Goursat reconstruction. -/
def EarlierLocal {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (i : ActionIndex) (b : ℕ)
    (L : Subgroup (sourceAction i × Equiv.Perm (Fin b))) : Prop :=
  ∃ j : Fin r,
    Earlier (2 * pairCount i + b) j
      (relabelSubgroup finSumFinEquiv
        (L.map (fusionOrbitAction (sourceAction i))))

/-- The exact remaining application-specific bridge to the already ordered
UP owner.  It is deliberately specialized to the payload constructed from
the chosen physical pair frame.  The historical E7 theorem concerns this
actual section; it does not assert recognition of an arbitrary payload with
the same source action and normal axis. -/
def OwnerRecognizes {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput) :
    Prop :=
  ∀ (i : ActionIndex)
    (N : {N : Subgroup (sourceAction i) // N.Normal})
    (_hcut : FixedCutUPCertified
      (axisPayload hTracey hExceptional i N).M (pairCount i)),
        ∀ b (J : Subgroup (Equiv.Perm (Fin b)))
          (β : GroupEpimorphism J (sourceAction i ⧸ N.1)),
          EarlierLocal Earlier i b (fusionFullGoursatEncode N J β).1

/-- Once the UP owner recognizes the checked cut, every axis chooses the
earlier-owner branch.  The capacity payload is used to prove recognition and
is then deliberately not charged as a new recurrence row. -/
noncomputable def axisOutcome_of_ownerRecognition
    {r : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hRecognizes : OwnerRecognizes Earlier hTracey hExceptional)
    (i : ActionIndex)
    (N : {N : Subgroup (sourceAction i) // N.Normal}) :
    Non2OriginalFusionAxisOutcome (pairCount i) (sourceAction i) N
      (EarlierLocal Earlier i) := by
  let A := axisPayload hTracey hExceptional i N
  exact .earlier (hRecognizes i N
    (axisPayload_fixedCutUPCertified hTracey hExceptional i N))

/-- Exact zero-payment conclusion for the appended residual owner. -/
theorem residualEpiCount_eq_zero_of_ownerRecognition
    {r b : ℕ}
    (Earlier : ∀ d, Fin r → Subgroup (Equiv.Perm (Fin d)) → Prop)
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hRecognizes : OwnerRecognizes Earlier hTracey hExceptional)
    (i : ActionIndex)
    (N : {N : Subgroup (sourceAction i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount (sourceAction i)
        (ordinaryFirstOwnerLocalPredicate (sourceAction i)
          (ownerOrResidualEligible Earlier (2 * pairCount i + b))
          (Fin.last r)) N J = 0 := by
  apply fusionSurvivingEpiCount_residual_eq_zero_of_earlierOwned
    Earlier (sourceAction i) N J
  intro β
  exact hRecognizes i N
    (axisPayload_fixedCutUPCertified hTracey hExceptional i N) b J β

end Non2UnipotentPrefixFiniteMenu

end SymmetricSubgroupAsymptotics

end
