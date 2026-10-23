import SymmetricSubgroupAsymptotics.CFSGInvolutionNormPairCoordinates
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormPairRepresentatives
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A literal 26-vector orbit-sum basis for the actual norm-image module
in characteristic two. Coverage uses only the already complete E6 root
menu and the selected representative certificates. No faithfulness or
exceptional-root covariance is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoNormBasis
open CFSGFFourE6NormPairRepresentatives CFSGFFourE6CharacteristicTwoNormImage
open CFSGInvolutionNormPairCoordinates CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6WeylChamber CFSGTwistedE6DiagramRootOrthogonality
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGNormTwoCoordinateDiagramIndices CFSGSerreDiagram
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
private instance : Fintype PairIndex := by unfold PairIndex;infer_instance

private def rootRepresentative (r:rootRepresentatives) : Roots CartanMatrix.E₆ :=
  ⟨r.val,rootRepresentatives_norm r.val r.property⟩

private theorem diagramIndex_simple (j:Fin 6) :
    diagramIndex (Sum.inl (E6Index j))=Sum.inl (E6Index (e6Permutation j)) :=
  congrArg (fun s:E6Base.support=>(Sum.inl s:GeckIndex))
    (supportPermutation_simple CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos e6Permutation j)

private theorem diagramRoot_val (r:Roots CartanMatrix.E₆) :
    (diagramRoot r).val=twistVector r.val := by
  funext j
  exact diagramRoot_coordinate r j

theorem selectedRepresentative_injective : Function.Injective selectedRepresentative := by
  intro a b he
  rcases a with i|r <;> rcases b with j|s
  · have hij:i=j := cartanRepresentative_injective (E6Index.injective (Sum.inl.inj he))
    exact congrArg Sum.inl hij
  · change (Sum.inl (E6Index (cartanRepresentative i)):GeckIndex)=Sum.inr (rootRepresentative s) at he
    cases he
  · change (Sum.inr (rootRepresentative r):GeckIndex)=Sum.inl (E6Index (cartanRepresentative j)) at he
    cases he
  · change (Sum.inr (rootRepresentative r):GeckIndex)=Sum.inr (rootRepresentative s) at he
    have hroot:rootRepresentative r=rootRepresentative s := Sum.inr.inj he
    have hrs:r=s := Subtype.ext (congrArg (fun t:Roots CartanMatrix.E₆=>t.val) hroot)
    exact congrArg Sum.inr hrs

theorem selectedRepresentative_disjoint (a b:PairIndex) :
    selectedRepresentative a≠diagramIndex (selectedRepresentative b) := by
  intro he
  rcases a with i|r <;> rcases b with j|s
  · change (Sum.inl (E6Index (cartanRepresentative i)):GeckIndex)=
      diagramIndex (Sum.inl (E6Index (cartanRepresentative j))) at he
    rw [diagramIndex_simple] at he
    exact cartanRepresentative_disjoint i j (E6Index.injective (Sum.inl.inj he))
  · change (Sum.inl (E6Index (cartanRepresentative i)):GeckIndex)=
      Sum.inr (diagramRoot (rootRepresentative s)) at he
    cases he
  · change (Sum.inr (rootRepresentative r):GeckIndex)=
      diagramIndex (Sum.inl (E6Index (cartanRepresentative j))) at he
    rw [diagramIndex_simple] at he
    cases he
  · change (Sum.inr (rootRepresentative r):GeckIndex)=Sum.inr (diagramRoot (rootRepresentative s)) at he
    have hv:r.val=twistVector s.val :=
      (congrArg Subtype.val (Sum.inr.inj he)).trans (diagramRoot_val (rootRepresentative s))
    exact rootRepresentatives_disjoint r.val r.property s.val s.property hv

theorem selectedRepresentative_cover (x:GeckIndex) :
    diagramIndex x=x ∨ ∃j:PairIndex,x=selectedRepresentative j∨x=diagramIndex (selectedRepresentative j) := by
  cases x with
  | inl x=>
    obtain ⟨i,rfl⟩ := E6Index.surjective x
    rcases cartanRepresentative_cover i with hf|⟨j,hj|hj⟩
    · left
      rw [diagramIndex_simple]
      exact congrArg (fun k:Fin 6=>(Sum.inl (E6Index k):GeckIndex)) hf
    · right
      exact ⟨Sum.inl j,Or.inl (congrArg (fun k:Fin 6=>(Sum.inl (E6Index k):GeckIndex)) hj)⟩
    · right
      refine ⟨Sum.inl j,Or.inr ?_⟩
      change (Sum.inl (E6Index i):GeckIndex)=diagramIndex (Sum.inl (E6Index (cartanRepresentative j)))
      rw [diagramIndex_simple]
      exact congrArg (fun k:Fin 6=>(Sum.inl (E6Index k):GeckIndex)) hj
  | inr k=>
    have hk := CFSGNormTwoCoordinateFiniteRootMenu.root_mem_menu CartanMatrix.E₆
      CartanMatrix.E₆_diag CartanMatrix.E₆_transpose E6_positive_definite
      CartanMatrix.E₆_off_diag_nonpos CFSGE6FiniteRootMenu.menu
      CFSGE6FiniteRootMenu.negative_simple_mem CFSGE6FiniteRootMenu.reflection_closed k
    rcases rootRepresentatives_cover k.val hk with hf|hr|hr
    · left
      change (Sum.inr (diagramRoot k):GeckIndex)=Sum.inr k
      apply congrArg (fun r:Roots CartanMatrix.E₆=>(Sum.inr r:GeckIndex))
      exact Subtype.ext ((diagramRoot_val k).trans hf)
    · right
      exact ⟨Sum.inr ⟨k.val,hr⟩,Or.inl rfl⟩
    · let r:rootRepresentatives := ⟨twistVector k.val,hr⟩
      have he:selectedRepresentative (Sum.inr r)=diagramIndex (Sum.inr k) := by
        change (Sum.inr (rootRepresentative r):GeckIndex)=Sum.inr (diagramRoot k)
        apply congrArg (fun t:Roots CartanMatrix.E₆=>(Sum.inr t:GeckIndex))
        exact Subtype.ext (diagramRoot_val k).symm
      right
      refine ⟨Sum.inr r,Or.inr ?_⟩
      rw [he,diagramIndex_involutive]

def normCoordinateEquiv (K:Type) [Field K] [CharP K 2] :
    characteristicNormImage K≃ₗ[K](PairIndex→K) :=
  normPairEquiv (R:=K) diagramIndex diagramIndex_involutive selectedRepresentative
    selectedRepresentative_injective selectedRepresentative_disjoint selectedRepresentative_cover

theorem normCoordinateEquiv_apply (K:Type) [Field K] [CharP K 2]
    (x:characteristicNormImage K) (j:PairIndex) :
    normCoordinateEquiv K x j=x.val (selectedRepresentative j) := rfl

def normBasis (K:Type) [Field K] [CharP K 2] :
    Module.Basis PairIndex K (characteristicNormImage K) :=
  (Pi.basisFun K PairIndex).map (normCoordinateEquiv K).symm

theorem normBasis_val (K:Type) [Field K] [CharP K 2] (j:PairIndex) :
    (normBasis K j).val=Pi.single (selectedRepresentative j) 1+
      diagramVector K (Pi.single (selectedRepresentative j) 1) := by
  simp only [normBasis,Module.Basis.map_apply,Pi.basisFun_apply]
  change ((normCoordinateEquiv K).symm (Pi.single j 1)).val=_
  have hj : normCoordinateEquiv K
      (pairVector (R:=K) diagramIndex selectedRepresentative j)=Pi.single j 1 :=
    coordinates_pairVector diagramIndex selectedRepresentative selectedRepresentative_injective
      selectedRepresentative_disjoint j
  have hh := congrArg (normCoordinateEquiv K).symm hj
  rw [LinearEquiv.symm_apply_apply] at hh
  rw [←hh]
  rfl

theorem characteristicNormImage_finrank (K:Type) [Field K] [CharP K 2] :
    Module.finrank K (characteristicNormImage K)=26 := by
  rw [Module.finrank_eq_card_basis (normBasis K),←Nat.card_eq_fintype_card,pairIndex_card]

end SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoNormBasis
