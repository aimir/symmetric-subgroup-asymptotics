import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralStepEntries
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoefficientPilot
import SymmetricSubgroupAsymptotics.CFSGFFourIntegralMatrices

/-! Identification of the pilot's simple-step and divided-square
entries with the literal integral E6 Geck matrices. No field or
ordinary F4 simplicity is needed for these integer equalities. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientStepEntries
open CFSGFFourSerreMatrices CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6WeylChamber
open CFSGTwistedE6DiagramRootOrthogonality CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateDiagramIndices CFSGSerreDiagram CFSGNormTwoGeckColumns
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6FixedIndexRepresentatives
open CFSGFFourE6NormQuotientRootMatching CFSGFFourE6NormQuotientCoefficientPilot
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

def eraseGeck : GeckIndex→RawIndex
  | .inl i=>.inl (E6Index.symm i)
  | .inr r=>.inr r.val

theorem E6Index_val (i:Fin 6) : (E6Index i:Roots CartanMatrix.E₆).val=simpleVector i := rfl

private theorem E6Base_cartan (i j:Fin 6) :
    E6Base.cartanMatrix (E6Index i) (E6Index j)=CartanMatrix.E₆ i j :=
  coordinate_cartan CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
    E6_positive_definite CartanMatrix.E₆_off_diag_nonpos i j

theorem e6EZ_entry (i:Fin 6) (r s:GeckIndex) :
    e6EZ i r s=stepEntry i (eraseGeck r) (eraseGeck s) := by
  cases r with
  | inl r=>
    obtain ⟨j,rfl⟩:=E6Index.surjective r
    cases s with
    | inl s=>
      obtain ⟨k,rfl⟩:=E6Index.surjective s
      exact CFSGNormTwoGeckIntegralStepEntries.E_inl_inl CartanMatrix.E₆
        CartanMatrix.E₆_transpose E6_positive_definite E6Base (E6Index i) (E6Index j) (E6Index k)
    | inr s=>
      change CFSGGeckIntegralMatrices.E E6Base (E6Index i) (Sum.inl (E6Index j)) (Sum.inr s)=_
      simp only [CFSGNormTwoGeckIntegralStepEntries.E_inl_inr CartanMatrix.E₆
        CartanMatrix.E₆_transpose E6_positive_definite E6Base,E6Index_val,
        eraseGeck,Equiv.symm_apply_apply,stepEntry,Equiv.apply_eq_iff_eq]
  | inr r=>
    cases s with
    | inl s=>
      obtain ⟨j,rfl⟩:=E6Index.surjective s
      change CFSGGeckIntegralMatrices.E E6Base (E6Index i) (Sum.inr r) (Sum.inl (E6Index j))=_
      simp only [CFSGNormTwoGeckIntegralStepEntries.E_inr_inl CartanMatrix.E₆
        CartanMatrix.E₆_transpose E6_positive_definite E6Base,E6Index_val,E6Base_cartan,
        eraseGeck,Equiv.symm_apply_apply,stepEntry]
    | inr s=>
      change CFSGGeckIntegralMatrices.E E6Base (E6Index i) (Sum.inr r) (Sum.inr s)=_
      simp only [CFSGNormTwoGeckIntegralStepEntries.E_inr_inr CartanMatrix.E₆
        CartanMatrix.E₆_transpose E6_positive_definite E6Base,E6Index_val,eraseGeck,stepEntry]
      split_ifs <;> rfl

theorem e6SecondZ_entry (i:Fin 6) (r s:GeckIndex) :
    e6SecondZ i r s=secondEntry i (eraseGeck r) (eraseGeck s) := by
  have hn (k:Roots CartanMatrix.E₆) :
      k=negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index i) ↔
        k.val= -simpleVector i := by
    have he:(k=negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index i)) ↔
      k.val=(negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index i)).val :=
        Subtype.ext_iff
    simpa only [negative_val,E6Index_val] using he
  have hnsym (k:Roots CartanMatrix.E₆) :
      negativeIndex CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite (E6Index i)=k ↔
        k.val= -simpleVector i := by
    constructor
    · intro he
      exact (hn k).mp he.symm
    · intro he
      exact ((hn k).mpr he).symm
  have hpos (k:Roots CartanMatrix.E₆) :
      (E6Index i:Roots CartanMatrix.E₆)=k ↔ k.val=simpleVector i := by
    constructor
    · intro he
      rw [←he,E6Index_val]
    · intro he
      exact Subtype.ext ((E6Index_val i).trans he.symm)
  cases r with
  | inl r=>
    cases s <;>
      simp [e6SecondZ,CFSGNormTwoGeckIntegralQuadratic.positiveSecond,
        secondEntry,eraseGeck]
  | inr r=>
    cases s with
    | inl s=>
      simp [e6SecondZ,CFSGNormTwoGeckIntegralQuadratic.positiveSecond,
        secondEntry,eraseGeck]
    | inr s=>
      simp only [e6SecondZ,CFSGNormTwoGeckIntegralQuadratic.positiveSecond,Matrix.single_apply,
        Sum.inr.injEq,hpos,hnsym,eraseGeck,secondEntry]

theorem eraseGeck_selectedRepresentative (j:PairIndex) :
    eraseGeck (selectedRepresentative j)=normIndex j := by
  cases j <;> simp only [selectedRepresentative,eraseGeck,normIndex,Equiv.symm_apply_apply]

theorem eraseGeck_partnerRepresentative (j:PairIndex) :
    eraseGeck (diagramIndex (selectedRepresentative j))=partnerIndex (normIndex j) := by
  cases j with
  | inl i=>
    have h:=congrArg (fun s:E6Base.support=>(Sum.inl s:GeckIndex))
      (supportPermutation_simple CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
        e6Permutation (cartanRepresentative i))
    change diagramIndex (Sum.inl (E6Index (cartanRepresentative i)))=
      Sum.inl (E6Index (e6Permutation (cartanRepresentative i))) at h
    change eraseGeck (diagramIndex (Sum.inl (E6Index (cartanRepresentative i)) ))=_
    rw [h]
    simp only [eraseGeck,Equiv.symm_apply_apply,normIndex,partnerIndex,e6Permutation_apply]
  | inr r=>
    change (Sum.inr (diagramRoot (⟨r.val,rootRepresentatives_norm r.val r.property⟩:Roots CartanMatrix.E₆)).val:RawIndex)=
      Sum.inr (twistVector r.val)
    apply congrArg Sum.inr
    funext i
    exact diagramRoot_coordinate _ i

theorem eraseGeck_fixedRepresentative (j:PairIndex) :
    eraseGeck (fixedRepresentative (basisIndexDual j))=fixedIndex j := by
  cases j with
  | inl i=>simp only [basisIndexDual_inl,fixedRepresentative,eraseGeck,Equiv.symm_apply_apply,fixedIndex]
  | inr r=>rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientStepEntries
