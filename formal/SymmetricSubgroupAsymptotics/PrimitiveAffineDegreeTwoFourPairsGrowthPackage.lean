import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsLiteralEnvelope
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoRawExceptionalGrowth

/-!
# Raw quadratic reserve for every four-pair row

This file adds the one piece deliberately absent from the basic literal
package: a proof that its pre-pointing exceptional term has a fixed
quadratic deficit.  It is kept in a later module so the action-free envelope
and its transport remain usable without importing asymptotic estimates.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private theorem y1_rawExceptional_eq_rankTail
    {w : ℕ} {U : PreE7NonPairActionClass w}
    (b : ℕ) :
    PreE7Y1ActionCertificate.rawExceptional
        (w := w) (U := U) b =
      rankTail51RawExceptional
        (PreE7B6ActionCertificate.normalCount
          (preE7NonPairAction w U)) b := by
  unfold PreE7Y1ActionCertificate.rawExceptional
    rankTail51RawExceptional
  ring

private theorem central_rawExceptional_eq_rankTail
    {Q : Type} [Group Q] [Finite Q]
    (D : PreE7CentralProductRankTailData Q) (b : ℕ) :
    D.literalExceptionalEnvelope b =
      rankTail51RawExceptional
        (2 * PreE7CentralProductRankTailData.normalCount D) b := by
  rfl

namespace CertifiedFourPairEasyModel

/-- The easy four-pair rows retain the raw quadratic reserve.  The linear
and abstract-S4 rows have zero exceptional term; Y1 uses the common
`51/200` rank-tail square completion. -/
noncomputable def quotientGrowthPackage
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairEasyModel U) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction 8 U) := by
  cases M with
  | linear S =>
      cases S with
      | gl e h =>
          let P := (CertifiedFourPairEasyModel.linear (.gl e h)).quotientSummedPackage lit
          apply PreE7DegreeTwoPairQuotientGrowthPackage.ofZero P
          rfl
      | sl e h =>
          let P := (CertifiedFourPairEasyModel.linear (.sl e h)).quotientSummedPackage lit
          apply PreE7DegreeTwoPairQuotientGrowthPackage.ofZero P
          rfl
  | abstractSymmetricFour e =>
      let P := (CertifiedFourPairEasyModel.abstractSymmetricFour e).quotientSummedPackage lit
      apply PreE7DegreeTwoPairQuotientGrowthPackage.ofZero P
      rfl
  | repeatedNaturalA4 S =>
      refine
        { package :=
            (CertifiedFourPairEasyModel.repeatedNaturalA4 S).quotientSummedPackage lit
          exceptionalGrowth := ?_ }
      intro hcoarse
      let K : ℝ := PreE7B6ActionCertificate.normalCount
        (preE7NonPairAction 8 U)
      have hK : 0 ≤ K := by
        dsimp [K]
        exact Nat.cast_nonneg _
      have H := rankTail51RawExceptional_bound hcoarse hK
      change RawQuadraticExceptionalBound
        ((S.quotientSummedEnvelope lit).exceptionalRaw)
      have hfun :
          (S.quotientSummedEnvelope lit).exceptionalRaw =
            rankTail51RawExceptional K := by
        funext b
        exact y1_rawExceptional_eq_rankTail b
      rw [hfun]
      exact H

end CertifiedFourPairEasyModel

namespace CertifiedFourPairCharacterModel

/-- Character-interval rows have no correlated exceptional term. -/
noncomputable def quotientGrowthPackage
    {U : PreE7NonPairActionClass 8}
    (M : CertifiedFourPairCharacterModel U)
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction 8 U) := by
  apply PreE7DegreeTwoPairQuotientGrowthPackage.ofZero
    (M.quotientSummedPackage hZmud lit)
  rfl

end CertifiedFourPairCharacterModel

namespace PublishedFourPairCentralModel

/-- The two central-product rows use the same raw rank-tail deficit as Y1,
with their exact literal normal-menu coefficient. -/
noncomputable def quotientGrowthPackage
    {U : PreE7NonPairActionClass 8}
    (M : PublishedFourPairCentralModel U) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction 8 U) := by
  refine
    { package := M.quotientSummedPackage
      exceptionalGrowth := ?_ }
  intro hcoarse
  let K : ℝ := 2 * PreE7CentralProductRankTailData.normalCount M.literalData
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (by norm_num)
      (PreE7CentralProductRankTailData.normalCount_nonneg M.literalData)
  have H := rankTail51RawExceptional_bound hcoarse hK
  change RawQuadraticExceptionalBound
    ((M.literalData.quotientSummedEnvelope).exceptionalRaw)
  have hfun :
      (M.literalData.quotientSummedEnvelope).exceptionalRaw =
        rankTail51RawExceptional K := by
    funext b
    exact central_rawExceptional_eq_rankTail M.literalData b
  rw [hfun]
  exact H

end PublishedFourPairCentralModel

namespace PublishedDegreeTwoFourPairRow

/-- Every published nonbinary four-pair row now carries both its compressed
raw envelope and the quadratic reserve needed after affine prepending. -/
noncomputable def quotientGrowthPackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : PublishedDegreeTwoFourPairRow U) :
    PreE7DegreeTwoPairQuotientGrowthPackage
      (preE7NonPairAction 8 U) :=
  match M with
  | .easy M => M.quotientGrowthPackage lit
  | .central M => M.quotientGrowthPackage
  | .character M => M.quotientGrowthPackage hZmud lit

end PublishedDegreeTwoFourPairRow

/-- Growth package on the selected four-pair catalogue representative. -/
noncomputable def degreeTwoFourPairRepresentativeGrowthPackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (p : PreE7PairActionClass 4) :
    PreE7DegreeTwoPairQuotientGrowthPackage (preE7PairAction 4 p) := by
  simpa only [preE7FourPairNonPairAction_literal] using
    (Classical.choice (published p)).quotientGrowthPackage hZmud lit

/-- Literal block-native four-pair package, including its pre-pointing
quadratic exceptional reserve. -/
noncomputable def degreeTwoFourPairLiteralGrowthPackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 8))
    (F : BinaryPairFrame A (Fin 4)) :
    PreE7DegreeTwoPairQuotientGrowthPackage A := by
  let C := fourPairRepresentativeChart A hA htrans F
  exact (degreeTwoFourPairRepresentativeGrowthPackage hZmud lit published
    C.representative).comapEquiv C.sourceEquiv

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
