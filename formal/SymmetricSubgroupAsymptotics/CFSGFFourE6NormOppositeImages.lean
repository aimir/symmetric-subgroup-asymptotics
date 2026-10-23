import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientCoordinateRootActions
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOppositeIntersection
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight

/-! The norm26 images of the actual positive and negative folded parts
are disjoint. Both parts act as identity on associated graded coordinates;
equality of their restricted actions therefore fixes the entire norm basis.
No injectivity on either whole unipotent group is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6NormOppositeImages
open CFSGFFourSerreMatrices CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6DiagramRootOrthogonality CFSGTwistedE6WeylChamber CFSGSerreDiagram
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateHeight CFSGNormTwoGeckHeightSupport
open CFSGNormTwoGeckOppositeIntersection CFSGGradedMatrixSubgroups CFSGSerreQuadraticMatrix
open CFSGFFourE6CharacteristicTwoNormImage CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6NormPairRepresentatives
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance

def normSignedPart (K:Type) [Field K] (neg:Bool) :
    Subgroup (canonicalElementaryGroup realizationData K) :=
  (SignedUpper K neg).subgroupOf (canonicalElementaryGroup realizationData K)

def degree : Index→ℤ := weight CartanMatrix.E₆ CartanMatrix.E₆_transpose
  E6_positive_definite E6Base coordinateHeight

theorem diagram_degree (i:Index) : degree (diagramIndex i)=degree i := by
  cases i with
  | inl i=>rfl
  | inr r=>
    change (∑i:Fin 6,(diagramRoot r).val i)=∑i:Fin 6,r.val i
    simp only [diagramRoot_coordinate]
    exact Equiv.sum_comp e6Permutation (fun i=>r.val i)

private theorem diagram_single (K:Type) [Field K] (i:Index) :
    diagramVector K (Pi.single i (1:K))=(Pi.single (diagramIndex i) (1:K):Index→K) := by
  funext j
  change (Pi.single i (1:K):Index→K) (diagramIndex.symm j)=
    (Pi.single (diagramIndex i) (1:K):Index→K) j
  simp only [Pi.single_apply,Equiv.symm_apply_eq]

theorem norm_coordinate_basis (K:Type) [Field K] [CharP K 2]
    (g:canonicalElementaryGroup realizationData K) (j k:PairIndex) :
    normCoordinateEquiv K (normAction K g (normBasis K k)) j=
      (g.val:Matrix Index Index K) (selectedRepresentative j) (selectedRepresentative k)+
        (g.val:Matrix Index Index K) (selectedRepresentative j) (diagramIndex (selectedRepresentative k)) := by
  rw [normCoordinateEquiv_apply,normAction_val,normBasis_val,diagram_single,
    Matrix.mulVec_add,Matrix.mulVec_single_one,Matrix.mulVec_single_one]
  rfl

private theorem norm_identity (K:Type) [Field K] (j k:PairIndex) :
    (1:Matrix Index Index K) (selectedRepresentative j) (selectedRepresentative k)+
      (1:Matrix Index Index K) (selectedRepresentative j) (diagramIndex (selectedRepresentative k))=
        (Pi.single k (1:K):PairIndex→K) j := by
  have he:selectedRepresentative j=selectedRepresentative k ↔ j=k:=selectedRepresentative_injective.eq_iff
  simp only [Matrix.one_apply,if_neg (selectedRepresentative_disjoint j k),add_zero,he,Pi.single_apply]

theorem positive_norm_coordinate (K:Type) [Field K] [CharP K 2]
    (g:canonicalElementaryGroup realizationData K) (hg:g∈normSignedPart K false)
    (j k:PairIndex) (hle:degree (selectedRepresentative j)≤degree (selectedRepresentative k)) :
    normCoordinateEquiv K (normAction K g (normBasis K k)) j=(Pi.single k (1:K):PairIndex→K) j := by
  have hmem:g.val∈SignedUpper K false:=hg
  have hs:=positive_le_strict CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index coordinateHeight
    (simple_height CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) K hmem
  change ∀r s,degree r≤degree s→(g.val:Matrix Index Index K) r s=(1:Matrix Index Index K) r s at hs
  have hpartner:degree (selectedRepresentative j)≤degree (diagramIndex (selectedRepresentative k)) := by
    rw [diagram_degree]
    exact hle
  rw [norm_coordinate_basis,hs _ _ hle,hs _ _ hpartner]
  exact norm_identity K j k

theorem negative_norm_coordinate (K:Type) [Field K] [CharP K 2]
    (g:canonicalElementaryGroup realizationData K) (hg:g∈normSignedPart K true)
    (j k:PairIndex) (hle:degree (selectedRepresentative k)≤degree (selectedRepresentative j)) :
    normCoordinateEquiv K (normAction K g (normBasis K k)) j=(Pi.single k (1:K):PairIndex→K) j := by
  have hmem:g.val∈SignedUpper K true:=hg
  have hs:=negative_le_strict_opposite CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite
    E6Base E6Index coordinateHeight
    (simple_height CartanMatrix.E₆ CartanMatrix.E₆_diag CartanMatrix.E₆_transpose
      E6_positive_definite CartanMatrix.E₆_off_diag_nonpos) K hmem
  change ∀r s,-degree r≤ -degree s→(g.val:Matrix Index Index K) r s=(1:Matrix Index Index K) r s at hs
  have hanti:-degree (selectedRepresentative j)≤ -degree (selectedRepresentative k):=by omega
  have hpartner:-degree (selectedRepresentative j)≤ -degree (diagramIndex (selectedRepresentative k)) := by
    rw [diagram_degree]
    exact hanti
  rw [norm_coordinate_basis,hs _ _ hanti,hs _ _ hpartner]
  exact norm_identity K j k

private theorem normBasis_coordinates (K:Type) [Field K] [CharP K 2] (k:PairIndex) :
    normCoordinateEquiv K (normBasis K k)=(Pi.single k (1:K):PairIndex→K) := by
  simp only [normBasis,Module.Basis.map_apply,Pi.basisFun_apply,LinearEquiv.apply_symm_apply]

theorem norm_action_eq_one_of_opposite (K:Type) [Field K] [CharP K 2]
    (u v:canonicalElementaryGroup realizationData K)
    (hu:u∈normSignedPart K false) (hv:v∈normSignedPart K true)
    (he:normAction K u=normAction K v) : normAction K u=1 := by
  have hlin:(normAction K u).toLinearMap=LinearMap.id := by
    apply (normBasis K).ext
    intro k
    apply (normCoordinateEquiv K).injective
    funext j
    change normCoordinateEquiv K (normAction K u (normBasis K k)) j=
      normCoordinateEquiv K (normBasis K k) j
    rw [normBasis_coordinates]
    by_cases hle:degree (selectedRepresentative j)≤degree (selectedRepresentative k)
    · exact positive_norm_coordinate K u hu j k hle
    · rw [he]
      exact negative_norm_coordinate K v hv j k (by omega)
  apply LinearEquiv.ext
  intro x
  exact LinearMap.congr_fun hlin x

theorem norm_opposite_action_inf (K:Type) [Field K] [CharP K 2] :
    (normSignedPart K false).map (normAction K)⊓
      (normSignedPart K true).map (normAction K)=⊥ := by
  apply le_antisymm _ bot_le
  rintro a ⟨⟨u,hu,rfl⟩,v,hv,he⟩
  exact Subgroup.mem_bot.mpr (norm_action_eq_one_of_opposite K u v hu hv he.symm)

end SymmetricSubgroupAsymptotics.CFSGFFourE6NormOppositeImages
