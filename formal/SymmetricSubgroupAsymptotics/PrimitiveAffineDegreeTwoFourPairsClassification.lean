import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsCentralSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsEasySource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsCharacterSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitivePairFrameExclusion

/-!
# Published four-pair action-row correspondence

Butler--McKay's transitive degree-eight catalogue, restricted to actions
with an invariant system of four pairs and nonbinary image, has ten rows.
The finite correspondence identifies each literal row with one of the
three independently proved source constructors below: LIN/S4/Y1, the two
central products, or the unique-minimal character interval.

The type `PublishedDegreeTwoFourPairClassification` is the sole finite
catalogue boundary in this slice.  It contains no numerical inequality:
all source and asymptotic estimates are constructed by the imported Lean
theorems after the row has been identified.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The three theorem-backed destinations of the ten published rows. -/
inductive PublishedDegreeTwoFourPairRow
    (U : PreE7NonPairActionClass 8) : Type 1
  | easy (model : CertifiedFourPairEasyModel U)
  | central (model : PublishedFourPairCentralModel U)
  | character (model : CertifiedFourPairCharacterModel U)

/-- At width eight the four residual pair widths are arithmetically
impossible.  Thus a pre-E7 four-pair representative canonically belongs to
the non-pair residual action index used by the numerical owners. -/
def preE7FourPairNonPairAction
    (p : PreE7PairActionClass 4) : PreE7NonPairActionClass 8 :=
  ⟨p.1, fun d hd => by
    cases d <;>
      norm_num [PreE7ResidualPairCountLabel.pairCount] at hd⟩

@[simp] theorem preE7FourPairNonPairAction_literal
    (p : PreE7PairActionClass 4) :
    preE7NonPairAction 8 (preE7FourPairNonPairAction p) =
      preE7PairAction 4 p :=
  rfl

/-- Exact Butler--McKay correspondence on the degree-eight pair-action
representative.  The pair frame is part of `p`; the output contains only the
structural row certificate used by one of the independently proved counting
theorems. -/
def PublishedDegreeTwoFourPairClassification : Prop :=
  ∀ p : PreE7PairActionClass 4,
    Nonempty (PublishedDegreeTwoFourPairRow
      (preE7FourPairNonPairAction p))

namespace PublishedDegreeTwoFourPairRow

noncomputable def source
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : PublishedDegreeTwoFourPairRow U) :
    PreE7RankTailSourceOrYonedaTopData 8 U :=
  match M with
  | .easy M => M.source
  | .central M => M.source
  | .character M => M.source hZmud lit

noncomputable def quotientSummedEnvelope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : PublishedDegreeTwoFourPairRow U) :
    PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction 8 U) :=
  match M with
  | .easy M => M.quotientSummedEnvelope lit
  | .central M => M.quotientSummedEnvelope
  | .character M => M.quotientSummedEnvelope hZmud lit

/-- The pre-padding row with its faithful comparator action retained. -/
noncomputable def quotientSummedPackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    {U : PreE7NonPairActionClass 8}
    (M : PublishedDegreeTwoFourPairRow U) :
    PreE7DegreeTwoPairQuotientSummedPackage
      (preE7NonPairAction 8 U) :=
  match M with
  | .easy M => M.quotientSummedPackage lit
  | .central M => M.quotientSummedPackage
  | .character M => M.quotientSummedPackage hZmud lit

end PublishedDegreeTwoFourPairRow

/-- The raw compressed envelope on the actual pair representative.  This is
the pre-padding endpoint consumed after `representative_cover`. -/
noncomputable def degreeTwoFourPairRepresentativeEnvelope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (p : PreE7PairActionClass 4) :
    PreE7DegreeTwoPairQuotientSummedEnvelope (preE7PairAction 4 p) := by
  simpa only [preE7FourPairNonPairAction_literal] using
    (Classical.choice (published p)).quotientSummedEnvelope hZmud lit

/-- The representative package, including the comparator action needed by
the degree-three affine prepend. -/
noncomputable def degreeTwoFourPairRepresentativePackage
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (p : PreE7PairActionClass 4) :
    PreE7DegreeTwoPairQuotientSummedPackage (preE7PairAction 4 p) := by
  simpa only [preE7FourPairNonPairAction_literal] using
    (Classical.choice (published p)).quotientSummedPackage hZmud lit

/-- Dispatch a classified row to its fully proved source theorem. -/
noncomputable def degreeTwoFourPairSource
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (U : PreE7NonPairActionClass 8)
    (basePoint : Fin 8)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction 8 U) basePoint)
    (hFibre : Nat.card block.Fibre = 2)
    (hPoints : Nat.card block.Points = 4) :
    PreE7RankTailSourceOrYonedaTopData 8 U := by
  let F : BinaryPairFrame (preE7NonPairAction 8 U) (Fin 4) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction 8 U) block hFibre).reindex
        (Finite.equivFinOfCardEq hPoints)
  let p : PreE7PairActionClass 4 := ⟨U.1, ⟨F⟩⟩
  have hUp : preE7FourPairNonPairAction p = U := Subtype.ext rfl
  rw [← hUp]
  exact (Classical.choice (published p)).source hZmud lit

/-- The same classification before physical pointing.  This is the API
used when a ternary elementary layer is prepended to the literal signed
pair quotient. -/
noncomputable def degreeTwoFourPairQuotientSummedEnvelope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (lit : PreE7CharacterLiterature)
    (published : PublishedDegreeTwoFourPairClassification)
    (U : PreE7NonPairActionClass 8)
    (basePoint : Fin 8)
    (block : OriginalMinimalBlock
      (A := preE7NonPairAction 8 U) basePoint)
    (hFibre : Nat.card block.Fibre = 2)
    (hPoints : Nat.card block.Points = 4) :
    PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction 8 U) := by
  let F : BinaryPairFrame (preE7NonPairAction 8 U) (Fin 4) :=
    (OriginalMinimalBlock.pairFrameOfFibreCardTwo
      (A := preE7NonPairAction 8 U) block hFibre).reindex
        (Finite.equivFinOfCardEq hPoints)
  let p : PreE7PairActionClass 4 := ⟨U.1, ⟨F⟩⟩
  have hUp : preE7FourPairNonPairAction p = U := Subtype.ext rfl
  rw [← hUp]
  exact (Classical.choice (published p)).quotientSummedEnvelope hZmud lit

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
