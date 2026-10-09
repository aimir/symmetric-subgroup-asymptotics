import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow0ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow1ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow2ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow3ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRows4To7ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow8ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow9ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop8GeneratedTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop9GeneratedTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop10GeneratedTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow20ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow21ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop13GeneratedTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow23ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop15GeneratedTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop16GeneratedTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameTop17GeneratedTable
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow27ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow28ActualBinding
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightFrameRow29ActualBinding

/-!
# Complete eligible eight-block frame catalogue

The thirty checked frame rows lie above twenty transitive degree-eight tops.
Four further nonbinary transitive tops have no point-stabilizer quotient of
order three, or noncommutative order six, and hence cannot occur in the
degree-four zero-core lane.  The published degree-eight correspondence is
therefore stated in its invariant eligible form: a transitive top carrying
the required local quotient is conjugate, after relabelling, to one of the
twenty literal checked tops.

This file performs the sole twenty-way dispatch.  Every selected branch is
then discharged by a kernel-complete local catalogue and its checked frame
registry; the published input chooses only the permutation top.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

/-- Labels inherited from the transitive-group catalogue.  Tops 18, 20,
23 and 24 are the four ineligible classes and therefore do not occur. -/
inductive DegreeEightEligibleTop where
  | top1 | top2 | top3 | top4 | top5 | top6 | top7 | top8 | top9 | top10
  | top11 | top12 | top13 | top14 | top15 | top16 | top17
  | top19 | top21 | top22

/-- The twenty eligible literal degree-eight tops. -/
def degreeEightEligibleLiteralTop :
    DegreeEightEligibleTop → Subgroup (Equiv.Perm (Fin 8))
  | .top1 => PrimitiveAffineEightFrameRow0LiteralLocalRow.LiteralAction
  | .top2 => PrimitiveAffineEightFrameRow1LiteralLocalRow.LiteralAction
  | .top3 => PrimitiveAffineEightFrameRow2LiteralLocalRow.LiteralAction
  | .top4 => PrimitiveAffineEightFrameRow3LiteralLocalRow.LiteralAction
  | .top5 => PrimitiveAffineEightFrameRows4To7LocalCatalogue.LiteralAction
  | .top6 => PrimitiveAffineEightFrameRow8LiteralLocalRow.LiteralAction
  | .top7 => PrimitiveAffineEightFrameRow9LiteralLocalRow.LiteralAction
  | .top8 => PrimitiveAffineEightFrameTop8GeneratedTable.topData.literalAction
  | .top9 => PrimitiveAffineEightFrameTop9GeneratedTable.topData.literalAction
  | .top10 => PrimitiveAffineEightFrameTop10GeneratedTable.topData.literalAction
  | .top11 => PrimitiveAffineEightFrameRow20LiteralLocalRow.LiteralAction
  | .top12 => PrimitiveAffineEightFrameRow21LiteralLocalRow.LiteralAction
  | .top13 => PrimitiveAffineEightFrameTop13GeneratedTable.topData.literalAction
  | .top14 => PrimitiveAffineEightFrameRow23LiteralLocalRow.LiteralAction
  | .top15 => PrimitiveAffineEightFrameTop15GeneratedTable.topData.literalAction
  | .top16 => PrimitiveAffineEightFrameTop16GeneratedTable.topData.literalAction
  | .top17 => PrimitiveAffineEightFrameTop17GeneratedTable.topData.literalAction
  | .top19 => PrimitiveAffineEightFrameRow27LiteralLocalRow.LiteralAction
  | .top21 => PrimitiveAffineEightFrameRow28LiteralLocalRow.LiteralAction
  | .top22 => PrimitiveAffineEightFrameRow29LiteralLocalRow.LiteralAction

/-- Published finite degree-eight correspondence in the exact form needed
by the frame consumer.  The extra hypothesis is invariant: one point
stabilizer has an onto image of order three or a noncommutative image of
order six.  It removes precisely `2^3:C7`, `AGL(3,2)`, `A8`, and `S8` from
the twenty-four nonbinary transitive classes. -/
def PublishedDegreeEightEligibleFrameClassification : Prop :=
  ∀ (X : Type) [Fintype X]
    (T : Subgroup (Equiv.Perm X)),
    Nat.card X = 8 →
    PermutationSubgroupTransitive T →
    ¬ IsPGroup 2 T →
    (∃ (x : X) (L : Type) (_ : Group L) (_ : Finite L)
      (f : MulAction.stabilizer T x →* L),
      Function.Surjective f ∧
        (Nat.card L = 3 ∨
          (Nat.card L = 6 ∧ ¬ IsMulCommutative L))) →
    ∃ (i : DegreeEightEligibleTop) (pointEquiv : X ≃ Fin 8)
      (conjugator : Equiv.Perm (Fin 8)),
      MulAut.conj conjugator • relabelSubgroup pointEquiv T =
        degreeEightEligibleLiteralTop i

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance completeEightFramePrimeFact : Fact P.p.Prime :=
  (chart block P).primeFact

/-- Computationally usable packaging of the published eligible-top
selection.  The existence theorem remains a proposition; this structure is
chosen noncomputably only after that theorem has supplied the row. -/
structure DegreeEightEligibleTopMatch where
  index : DegreeEightEligibleTop
  pointEquiv : block.Points ≃ Fin 8
  conjugator : Equiv.Perm (Fin 8)
  conjugated :
    MulAut.conj conjugator • relabelSubgroup pointEquiv block.Top =
      degreeEightEligibleLiteralTop index

/-- The actual zero-core top has the local quotient required by the
eligible degree-eight classifier. -/
theorem degreeFourZeroCoreTop_hasEligibleLocalQuotient
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥) :
    ∃ (x : block.Points) (L : Type) (_ : Group L) (_ : Finite L)
      (f : MulAction.stabilizer block.Top x →* L),
      Function.Surjective f ∧
        (Nat.card L = 3 ∨
          (Nat.card L = 6 ∧ ¬ IsMulCommutative L)) := by
  let x : block.Points := Classical.choice
    (Finite.card_pos_iff.mp (by
      have h := block.degrees_ge_two.2
      omega))
  refine ⟨x, LocalQuotient block P, inferInstance, inferInstance,
    degreeFourZeroCoreTopStabilizerLocalMap block P hr hD x,
    degreeFourZeroCoreTopStabilizerLocalMap_surjective block P hr hD x, ?_⟩
  rcases degreeFourZeroCoreTopStabilizerLocalTarget_card block P hr with
    h3 | h6
  · exact Or.inl h3
  · refine Or.inr ⟨h6, ?_⟩
    let C := chart block P
    have hp : P.p = 2 := degreeFour_profilePrime_eq_two block P hr
    have hV : Module.finrank (ZMod P.p) C.V = 2 := by
      change C.d = 2
      exact (degreeFour_translationDimension block P hr).2
    exact not_isMulCommutative_of_faithful_binary_plane_card_six_at
      hp (binaryAffineLocalLinearRepresentation block P).ρ h6 hV
      (binaryAffineLocalLinearRepresentation_injective block P)

/-- Select an eligible checked literal top for the actual degree-four
zero-core block action. -/
noncomputable def degreeFourZeroCoreEightEligibleTopMatch
    (published : PublishedDegreeEightEligibleFrameClassification)
    (hr : Nat.card block.Fibre = 4)
    (hD : degreeFourTernaryCore block P = ⊥)
    (hs : Nat.card block.Points = 8) :
    DegreeEightEligibleTopMatch block := by
  have htransitive : PermutationSubgroupTransitive block.Top := by
    letI : MulAction.IsPretransitive block.Top block.Points :=
      block.top_pretransitive
    intro x y
    obtain ⟨g, hxy⟩ := MulAction.exists_smul_eq block.Top x y
    exact ⟨g, g.property, hxy⟩
  exact Classical.choice (by
    rcases published block.Points block.Top hs htransitive
        (degreeFourZeroCoreTop_not_isPGroup_two block P hr hD)
        (degreeFourZeroCoreTop_hasEligibleLocalQuotient block P hr hD) with
      ⟨i, pointEquiv, conjugator, hconjugated⟩
    exact ⟨{
      index := i
      pointEquiv := pointEquiv
      conjugator := conjugator
      conjugated := hconjugated }⟩)

/-- The complete checked eight-block frame bound.  The classifier selects
one of twenty literal tops; the branch's complete local table selects the
correct row whenever several kernels lie above that top. -/
noncomputable def degreeFourZeroCoreEightFrameBounds_of_published
    (published : PublishedDegreeEightEligibleFrameClassification) :
    DegreeFourZeroCoreEightFrameBoundsInput := by
  intro w U basePoint block P _inst hr hD hs
  let M := degreeFourZeroCoreEightEligibleTopMatch
    block P published hr hD hs
  rcases M with ⟨i, pointEquiv, conjugator, hconjugated⟩
  cases i
  · exact PrimitiveAffineEightFrameRow0ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow1ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow2ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow3ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRows4To7ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow8ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow9ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameTop8GeneratedTable.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameTop9GeneratedTable.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameTop10GeneratedTable.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow20ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow21ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameTop13GeneratedTable.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow23ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameTop15GeneratedTable.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameTop16GeneratedTable.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameTop17GeneratedTable.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow27ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow28ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs
  · exact PrimitiveAffineEightFrameRow29ActualBinding.bounds block P
      pointEquiv conjugator hconjugated hr hD hs

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
