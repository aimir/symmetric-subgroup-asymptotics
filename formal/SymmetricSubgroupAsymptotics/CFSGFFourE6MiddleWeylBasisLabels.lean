import SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylColumnPilot
import SymmetricSubgroupAsymptotics.CFSGFFourE6NormQuotientOppositionLabels

/-! Exact identification of the selected computational 26 labels with
the proved norm-image basis, including the actual negative-label action.
This is finite label arithmetic, independent of any matrix-word claim. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylBasisLabels
open CFSGFFourE6MiddleWeylColumnPilot CFSGFFourE6NormPairRepresentatives
open CFSGFFourE6NormQuotientCoefficientPilot CFSGFFourE6NormQuotientOppositionLabels
local instance : Fintype PairIndex := by unfold PairIndex;infer_instance
local instance : DecidableEq PairIndex := by unfold PairIndex;infer_instance

def basisIndex : Fin 26→PairIndex := ![
    Sum.inl 0,
    Sum.inl 1,
    Sum.inr ⟨![-1,-1,-2,-2,-1,-1],by decide +kernel⟩,
    Sum.inr ⟨![-1,-1,-2,-2,-1,0],by decide +kernel⟩,
    Sum.inr ⟨![-1,-1,-1,-2,-1,0],by decide +kernel⟩,
    Sum.inr ⟨![-1,-1,-1,-1,-1,0],by decide +kernel⟩,
    Sum.inr ⟨![-1,-1,-1,-1,0,0],by decide +kernel⟩,
    Sum.inr ⟨![-1,0,-1,-1,-1,0],by decide +kernel⟩,
    Sum.inr ⟨![-1,0,-1,-1,0,0],by decide +kernel⟩,
    Sum.inr ⟨![-1,0,-1,0,0,0],by decide +kernel⟩,
    Sum.inr ⟨![-1,0,0,0,0,0],by decide +kernel⟩,
    Sum.inr ⟨![0,-1,-1,-1,0,0],by decide +kernel⟩,
    Sum.inr ⟨![0,0,-1,-1,0,0],by decide +kernel⟩,
    Sum.inr ⟨![0,0,-1,0,0,0],by decide +kernel⟩,
    Sum.inr ⟨![0,0,0,0,0,1],by decide +kernel⟩,
    Sum.inr ⟨![0,0,0,0,1,0],by decide +kernel⟩,
    Sum.inr ⟨![0,0,0,0,1,1],by decide +kernel⟩,
    Sum.inr ⟨![0,0,0,1,1,0],by decide +kernel⟩,
    Sum.inr ⟨![0,0,0,1,1,1],by decide +kernel⟩,
    Sum.inr ⟨![0,0,1,1,1,1],by decide +kernel⟩,
    Sum.inr ⟨![0,1,0,1,1,0],by decide +kernel⟩,
    Sum.inr ⟨![0,1,0,1,1,1],by decide +kernel⟩,
    Sum.inr ⟨![0,1,1,1,1,1],by decide +kernel⟩,
    Sum.inr ⟨![0,1,1,2,1,1],by decide +kernel⟩,
    Sum.inr ⟨![0,1,1,2,2,1],by decide +kernel⟩,
    Sum.inr ⟨![1,1,1,2,2,1],by decide +kernel⟩]

theorem normIndex_basisIndex : ∀i : Fin 26,normIndex (basisIndex i)=columnLabels i :=
  by decide +kernel

theorem normIndex_negative_basisIndex : ∀i : Fin 26,
    normIndex (negativePair (basisIndex i))=negativeLabel (columnLabels i) :=
  by decide +kernel

theorem basisIndex_bijective : Function.Bijective basisIndex := by
  constructor <;> decide +kernel

end SymmetricSubgroupAsymptotics.CFSGFFourE6MiddleWeylBasisLabels
