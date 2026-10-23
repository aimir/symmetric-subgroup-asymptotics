import SymmetricSubgroupAsymptotics.CFSGInvolutionNormImageAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6DiagramFixed
import SymmetricSubgroupAsymptotics.CFSGTwistedE6DiagramRootOrthogonality
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! The actual folded F4 matrices act on the image of 1+P in the
78-coordinate E6 Geck module, where P is the pinned diagram permutation.
This action needs no ordinary F4 simplicity. The dimension-26 assertion
in characteristic two and faithfulness are separate, unproved here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoNormImage
open CFSGFFourSerreMatrices CFSGFFourE6DiagramFixed
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6DiagramRootOrthogonality CFSGTwistedE6WeylChamber CFSGSerreDiagram
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix CFSGNormTwoCoordinateDiagramIndices
open CFSGInvolutionNormImageAction
local instance : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

abbrev Ambient (K:Type) := Index→K

def diagramVector (K:Type) [Field K] : Ambient K≃ₗ[K]Ambient K :=
  LinearEquiv.funCongrLeft K K diagramIndex.symm

theorem diagramIndex_involutive : Function.Involutive diagramIndex := by
  intro x
  cases x with
  | inl x=>
    obtain ⟨i,rfl⟩ := E6Index.surjective x
    have hs (j:Fin 6) : diagramIndex (Sum.inl (E6Index j))=Sum.inl (E6Index (e6Permutation j)) := by
      change (Sum.inl (supportPermutation CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
        e6Permutation (E6Index j)):GeckIndex)=_
      exact congrArg (fun s:E6Base.support=>(Sum.inl s:GeckIndex))
        (supportPermutation_simple CartanMatrix.E₆ CartanMatrix.E₆_diag
          CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos
          e6Permutation j)
    rw [hs,hs,diagramPermutation_involutive]
  | inr k=>
    change (Sum.inr (diagramRoot (diagramRoot k)):GeckIndex)=Sum.inr k
    apply congrArg (fun r:Roots CartanMatrix.E₆=>(Sum.inr r:GeckIndex))
    apply Subtype.ext
    funext i
    change k.val (e6Permutation.symm (e6Permutation.symm i))=k.val i
    rw [diagramPermutation_symm,diagramPermutation_symm,diagramPermutation_involutive]

theorem diagramVector_involutive (K:Type) [Field K] : Function.Involutive (diagramVector K) := by
  have hs (i:GeckIndex) : diagramIndex.symm i=diagramIndex i := by
    apply diagramIndex.injective
    rw [Equiv.apply_symm_apply,diagramIndex_involutive]
  intro x
  funext i
  change x (diagramIndex.symm (diagramIndex.symm i))=x i
  rw [hs,hs,diagramIndex_involutive]

def characteristicNormImage (K:Type) [Field K] : Submodule K (Ambient K) :=
  normImage (diagramVector K).toLinearMap

def matrixLinearEquiv (K:Type) [Field K] :
    (Matrix Index Index K)ˣ≃*(Ambient K≃ₗ[K]Ambient K) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Ambient K))

def ambientAction (K:Type) [Field K] :
    canonicalElementaryGroup realizationData K→*(Ambient K≃ₗ[K]Ambient K) :=
  (matrixLinearEquiv K).toMonoidHom.comp (canonicalElementaryGroup realizationData K).subtype

theorem ambientAction_apply (K:Type) [Field K]
    (g:canonicalElementaryGroup realizationData K) (x:Ambient K) :
    ambientAction K g x=(g.val:Matrix Index Index K)*ᵥx := rfl

private theorem reindex_fixed_commutes {I:Type*} [Fintype I] [DecidableEq I]
    (K:Type) [Field K] (p:Equiv.Perm I) (M:Matrix I I K)
    (hM:Matrix.reindex p p M=M) (x:I→K) :
    M*ᵥ(LinearEquiv.funCongrLeft K K p.symm x)=
      LinearEquiv.funCongrLeft K K p.symm (M*ᵥx) := by
  let P := LinearEquiv.funCongrLeft K K p.symm
  have hx : (P x)∘p=x := by
    funext i
    change x (p.symm (p i))=x i
    rw [Equiv.symm_apply_apply]
  calc
    M*ᵥP x=(Matrix.reindex p p M)*ᵥP x := congrArg (fun A:Matrix I I K=>A*ᵥP x) hM.symm
    _=(M*ᵥ((P x)∘p))∘p.symm := Matrix.submatrix_mulVec_equiv M (P x) p.symm p.symm
    _=P (M*ᵥx) := by rw [hx];rfl

theorem ambientAction_commutes (K:Type) [Field K]
    (g:canonicalElementaryGroup realizationData K) (x:Ambient K) :
    ambientAction K g (diagramVector K x)=diagramVector K (ambientAction K g x) := by
  have hf : unitTwist K (RingEquiv.refl K) g.val=g.val := foldedModel_le_diagramFixed K g.property
  have hv := congrArg (fun u:(Matrix Index Index K)ˣ=>(u:Matrix Index Index K)) hf
  change Matrix.reindex diagramIndex diagramIndex (g.val:Matrix Index Index K)=
    (g.val:Matrix Index Index K) at hv
  exact reindex_fixed_commutes K diagramIndex (g.val:Matrix Index Index K) hv x

def normAction (K:Type) [Field K] :
    canonicalElementaryGroup realizationData K→*
      (characteristicNormImage K≃ₗ[K]characteristicNormImage K) :=
  normImageAction (diagramVector K).toLinearMap (ambientAction K) (ambientAction_commutes K)

theorem normAction_val (K:Type) [Field K] (g:canonicalElementaryGroup realizationData K)
    (x:characteristicNormImage K) :
    (normAction K g x).val=(g.val:Matrix Index Index K)*ᵥx.val := rfl

theorem normImage_fixed (K:Type) [Field K] (x:characteristicNormImage K) :
    diagramVector K x.val=x.val :=
  CFSGInvolutionNormImageAction.normImage_fixed (diagramVector K).toLinearMap
    (diagramVector_involutive K) x

def foldedRoot (K:Type) [Field K] (neg:Bool) (i:Fin 4) (t:K) :
    canonicalElementaryGroup realizationData K :=
  ⟨canonicalRoot realizationData K neg i t,Subgroup.subset_closure ⟨neg,i,t,rfl⟩⟩

theorem normAction_root_val (K:Type) [Field K] (neg:Bool) (i:Fin 4) (t:K)
    (x:characteristicNormImage K) :
    (normAction K (foldedRoot K neg i t) x).val=
      (1+t • fieldRoot realizationData K neg i+t^2 • fieldSecond realizationData K neg i)*ᵥx.val := rfl

end SymmetricSubgroupAsymptotics.CFSGFFourE6CharacteristicTwoNormImage
