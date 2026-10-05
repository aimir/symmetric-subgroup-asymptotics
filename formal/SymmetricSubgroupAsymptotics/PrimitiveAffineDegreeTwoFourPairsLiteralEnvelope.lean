import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsClassification
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoQuotientEnvelopeTransport

/-!
# Literal four-pair envelope before action-index membership

An affine quotient reaches a literal nonbinary pair action.  It must not be
asserted to belong to the later non-pair residual index.  We first use the
ordinary conjugacy-class cover on its faithful eight-point pair action,
retain the resulting source-group equivalence, and only then invoke the
published ten-row correspondence on the representative.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The selected pair widths begin at forty-eight points, so every
nonbinary degree-eight representative lies on the pre-E7 side. -/
def degreeEightPreE7Action
    (i : Non2TransitiveActionClass (Fin 8)) : PreE7ActionClass 8 :=
  ⟨i, fun d hd => by
    cases d <;> norm_num [PairCountLabel.sourceDegree,
      PairCountLabel.pairCount] at hd⟩

/-- Conjugacy-class representative of a literal four-pair action, together
with the actual source-group equivalence induced by point relabelling. -/
structure FourPairRepresentativeChart
    (A : Subgroup (Equiv.Perm (Fin 8))) where
  representative : PreE7PairActionClass 4
  sourceEquiv : A ≃* preE7PairAction 4 representative

/-- Construct the chart by the complete nonbinary transitive representative
cover.  The supplied pair frame is relabelled on the same eight points. -/
noncomputable def fourPairRepresentativeChart
    (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 8))
    (F : BinaryPairFrame A (Fin 4)) : FourPairRepresentativeChart A := by
  let hcover :=
    Non2TransitiveActionClass.representative_cover A hA htrans
  let i : Non2TransitiveActionClass (Fin 8) := Classical.choose hcover
  let hi : ∃ c : Equiv.Perm (Fin 8),
      MulAut.conj c • A = i.representative :=
    Classical.choose_spec hcover
  let c : Equiv.Perm (Fin 8) := Classical.choose hi
  have hc : MulAut.conj c • A = i.representative :=
    Classical.choose_spec hi
  have hc' : relabelSubgroup c A = i.representative := by
    calc
      relabelSubgroup c A = MulAut.conj c • A := by
        change A.map c.permCongrHom.toMonoidHom = _
        rw [Subgroup.pointwise_smul_def]
        congr 1
      _ = i.representative := hc
  let F' : BinaryPairFrame i.representative (Fin 4) :=
    hc' ▸ F.relabelPoints c
  let p : PreE7PairActionClass 4 :=
    ⟨degreeEightPreE7Action i, ⟨F'⟩⟩
  exact
    { representative := p
      sourceEquiv := (BinaryPairFrame.sourceRelabelEquiv (U := A) c).trans
        (MulEquiv.subgroupCongr hc') }

/-- The complete raw quotient envelope on a literal four-pair action.  The
only classification input is the published ten-row correspondence on the
chosen representative; all counting is transported from the independently
proved row theorem. -/
noncomputable def degreeTwoFourPairLiteralEnvelope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 8))
    (F : BinaryPairFrame A (Fin 4)) :
    PreE7DegreeTwoPairQuotientSummedEnvelope A := by
  let C := fourPairRepresentativeChart A hA htrans F
  exact (degreeTwoFourPairRepresentativeEnvelope hZmud lit published
    C.representative).comapEquiv C.sourceEquiv

/-- The literal block-native package consumed by a later affine prepend.  It
retains the faithful action of the hidden comparator selected by the finite
four-pair row, before any ambient numerical margin is imposed. -/
noncomputable def degreeTwoFourPairLiteralPackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (A : Subgroup (Equiv.Perm (Fin 8)))
    (hA : ¬ IsPGroup 2 A)
    (htrans : MulAction.IsPretransitive A (Fin 8))
    (F : BinaryPairFrame A (Fin 4)) :
    PreE7DegreeTwoPairQuotientSummedPackage A := by
  let C := fourPairRepresentativeChart A hA htrans F
  exact (degreeTwoFourPairRepresentativePackage hZmud lit published
    C.representative).comapEquiv C.sourceEquiv

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
