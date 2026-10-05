import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoThreePairsClassification
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSelfEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairQuotientPackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRawExceptionalGrowth
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsLiteralEnvelope

/-!
# Block-native raw packages for the published three-pair slice

The degree-six classifier was originally stated on an action together with
one selected minimal block.  Affine prepending reaches the same object one
step earlier: a literal transitive nonbinary action with an actual frame of
three pairs.  This file states the Butler--McKay slice on that representative,
retains the smaller faithful comparator of every row, and transports the raw
complete-quotient envelope back to the literal group.

No physical pointing is performed here.  In particular the two central
product rows retain their source-summed binary-rank tail and its quadratic
reserve.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev A4 := NaturalA4ScalarFourHead.G

/-- A three-pair representative has degree six, hence misses every selected
and residual pair width in the pre-`E7` index. -/
def preE7ThreePairNonPairAction
    (p : PreE7PairActionClass 3) : PreE7NonPairActionClass 6 :=
  ⟨p.1, fun d hd => by
    cases d <;>
      norm_num [PreE7ResidualPairCountLabel.pairCount] at hd⟩

@[simp] theorem preE7ThreePairNonPairAction_literal
    (p : PreE7PairActionClass 3) :
    preE7NonPairAction 6 (preE7ThreePairNonPairAction p) =
      preE7PairAction 3 p :=
  rfl

/-- Exact Butler--McKay correspondence on the degree-six representative
already equipped with its displayed three-pair frame. -/
def PublishedDegreeTwoThreePairRepresentativeClassification : Prop :=
  ∀ p : PreE7PairActionClass 3,
    Nonempty (PublishedDegreeTwoThreePairModel
      (preE7ThreePairNonPairAction p))

namespace PublishedThreePairEasyModel

/-- The raw complete quotient moment for an easy row is the target's own
moment.  The compression is carried by the separately retained faithful
action below. -/
noncomputable def quotientSummedPackage
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairEasyModel U) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction 6 U) := by
  let E := preE7DegreeTwoPairQuotientSelfEnvelope
    (preE7NonPairAction 6 U)
  cases M with
  | cyclicSix e =>
      exact
        { envelope := E
          v := 5
          action := cyclicSixComparatorAction.comp e.toMonoidHom
          action_injective := cyclicSixComparatorAction_injective.comp
            e.injective }
  | alternatingFour e =>
      exact
        { envelope := E
          v := 4
          action := A4.subtype.comp e.toMonoidHom
          action_injective := Subtype.val_injective.comp e.injective }
  | symmetricThree e =>
      exact
        { envelope := E
          v := 3
          action := e.toMonoidHom
          action_injective := e.injective }
  | symmetricThreeTimesTwo e =>
      exact
        { envelope := E
          v := 5
          action := s3c2Action.comp e.toMonoidHom
          action_injective := s3c2Action_injective.comp e.injective }
  | abstractSymmetricFour e =>
      exact
        { envelope := E
          v := 4
          action := e.toMonoidHom
          action_injective := e.injective }

/-- The wrapper around the identity complete-moment envelope does not change
its zero exceptional term.  This proposition is proved by row cases without
destructing the data-valued growth package below. -/
theorem quotientSummedPackage_exceptionalRaw
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairEasyModel U) :
    M.quotientSummedPackage.envelope.exceptionalRaw = fun _ => 0 := by
  cases M <;>
    rfl

/-- Easy rows have no correlated exceptional term. -/
noncomputable def quotientGrowthPackage
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairEasyModel U) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction 6 U) :=
  PreE7DegreeTwoPairQuotientGrowthPackage.ofZero
    M.quotientSummedPackage M.quotientSummedPackage_exceptionalRaw

end PublishedThreePairEasyModel

namespace PublishedThreePairCentralModel

/-- Central rows retain the actual degree-five quotient action. -/
noncomputable def quotientSummedPackage
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairCentralModel U) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction 6 U) where
  envelope := M.quotientSummedEnvelope
  v := 5
  action := M.literalData.action
  action_injective := M.literalData.action_injective

private theorem rawExceptional_eq_rankTail
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairCentralModel U) (b : ℕ) :
    M.literalData.literalExceptionalEnvelope b =
      rankTail51RawExceptional
        (2 * PreE7CentralProductRankTailData.normalCount M.literalData) b := by
  rfl

/-- The common central-repeat tail retains the same raw quadratic deficit
before any later affine layer is prepended. -/
noncomputable def quotientGrowthPackage
    {U : PreE7NonPairActionClass 6}
    (M : PublishedThreePairCentralModel U) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction 6 U) := by
  refine
    { package := M.quotientSummedPackage
      exceptionalGrowth := ?_ }
  intro hcoarse
  let K : ℝ :=
    2 * PreE7CentralProductRankTailData.normalCount M.literalData
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num)
      (PreE7CentralProductRankTailData.normalCount_nonneg M.literalData)
  have H := rankTail51RawExceptional_bound hcoarse hK
  change RawQuadraticExceptionalBound
    (M.literalData.quotientSummedEnvelope.exceptionalRaw)
  have hfun :
      M.literalData.quotientSummedEnvelope.exceptionalRaw =
        rankTail51RawExceptional K := by
    funext b
    exact rawExceptional_eq_rankTail M b
  rw [hfun]
  exact H

end PublishedThreePairCentralModel

namespace PublishedDegreeTwoThreePairModel

noncomputable def quotientGrowthPackage
    {U : PreE7NonPairActionClass 6}
    (M : PublishedDegreeTwoThreePairModel U) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction 6 U) :=
  match M with
  | .easy M => M.quotientGrowthPackage
  | .central M => M.quotientGrowthPackage

end PublishedDegreeTwoThreePairModel

/-- Representative package selected by the published degree-six slice. -/
noncomputable def degreeTwoThreePairRepresentativeGrowthPackage
    (published : PublishedDegreeTwoThreePairRepresentativeClassification)
    (p : PreE7PairActionClass 3) :
    PreE7DegreeTwoPairQuotientGrowthPackage (preE7PairAction 3 p) := by
  simpa only [preE7ThreePairNonPairAction_literal] using
    (Classical.choice (published p)).quotientGrowthPackage

/-- Dispatch the same representative row to its already checked physical
owner source. -/
noncomputable def degreeTwoThreePairRepresentativeSource
    (published : PublishedDegreeTwoThreePairRepresentativeClassification)
    (p : PreE7PairActionClass 3) :
    PreE7RankTailSourceOrYonedaTopData 6
      (preE7ThreePairNonPairAction p) :=
  (Classical.choice (published p)).source

/-- Conjugacy representative of a literal nonbinary action on three pairs. -/
structure ThreePairRepresentativeChart
    (A : Subgroup (Equiv.Perm (Fin 6))) where
  representative : PreE7PairActionClass 3
  sourceEquiv : A ≃* preE7PairAction 3 representative

/-- Build the representative chart from the literal action and its retained
pair frame. -/
noncomputable def threePairRepresentativeChart
    (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 6))
    (F : BinaryPairFrame A (Fin 3)) : ThreePairRepresentativeChart A := by
  let hcover :=
    Non2TransitiveActionClass.representative_cover A hA htrans
  let i : Non2TransitiveActionClass (Fin 6) := Classical.choose hcover
  let hi : ∃ c : Equiv.Perm (Fin 6),
      MulAut.conj c • A = i.representative :=
    Classical.choose_spec hcover
  let c : Equiv.Perm (Fin 6) := Classical.choose hi
  have hc : MulAut.conj c • A = i.representative :=
    Classical.choose_spec hi
  have hc' : relabelSubgroup c A = i.representative := by
    calc
      relabelSubgroup c A = MulAut.conj c • A := by
        change A.map c.permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = i.representative := hc
  let F' : BinaryPairFrame i.representative (Fin 3) :=
    hc' ▸ F.relabelPoints c
  let p : PreE7PairActionClass 3 :=
    ⟨⟨i, fun d hd => by
        cases d <;> norm_num [PairCountLabel.sourceDegree,
          PairCountLabel.pairCount] at hd⟩, ⟨F'⟩⟩
  exact
    { representative := p
      sourceEquiv := (BinaryPairFrame.sourceRelabelEquiv (U := A) c).trans
        (MulEquiv.subgroupCongr hc') }

/-- Literal actual-target package for a nonbinary three-pair action. -/
noncomputable def degreeTwoThreePairLiteralGrowthPackage
    (published : PublishedDegreeTwoThreePairRepresentativeClassification)
    (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 6))
    (F : BinaryPairFrame A (Fin 3)) :
    PreE7DegreeTwoPairQuotientGrowthPackage A := by
  let C := threePairRepresentativeChart A hA htrans F
  exact (degreeTwoThreePairRepresentativeGrowthPackage published
    C.representative).comapEquiv C.sourceEquiv

/-- Action-facing source for the original minimal block, using the same
representative classification as the literal package. -/
noncomputable def degreeTwoThreePairSource_of_representative
    (published : PublishedDegreeTwoThreePairRepresentativeClassification)
    (U : PreE7NonPairActionClass 6)
    (basePoint : Fin 6)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction 6 U) basePoint)
    (hFibre : Nat.card block.Fibre = 2)
    (hPoints : Nat.card block.Points = 3) :
    PreE7RankTailSourceOrYonedaTopData 6 U := by
  let F : BinaryPairFrame (preE7NonPairAction 6 U) (Fin 3) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction 6 U) block hFibre).reindex
        (Finite.equivFinOfCardEq hPoints)
  let p : PreE7PairActionClass 3 := ⟨U.1, ⟨F⟩⟩
  have hUp : preE7ThreePairNonPairAction p = U := Subtype.ext rfl
  rw [← hUp]
  exact degreeTwoThreePairRepresentativeSource published p

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
