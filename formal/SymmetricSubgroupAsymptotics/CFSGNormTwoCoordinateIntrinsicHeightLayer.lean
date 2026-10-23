import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerCoordinates
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateAllRootParameters

/-! Intrinsic exact-height coordinates use the ACTUAL root lines,
not independently chosen scalar charts. Their product is the literal
height-layer quotient; a single coordinate is exactly its root-line
inclusion. This permits twisted coordinate peeling without chart signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicHeightLayer
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositiveRootCardinality CFSGNormTwoCoordinateAllRootParameters
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateHeightLayerCoordinates
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j → A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local instance (K : Type) [Field K] (h : ℤ) :
    (heightTailInPositive A hd hs hp ho K h).Normal :=
  heightTail_normal_in_positive A hd hs hp ho K h

def rootParameterEquiv (K : Type) [Field K] (k : Roots A) :
    Multiplicative K ≃* rootSubgroup A hd hs hp ho K k :=
  (MonoidHom.ofInjective (selected_rootHom_injective A hd hs hp ho K k)).trans
    (MulEquiv.subgroupCongr (selectedRootHom_range A hd hs hp ho K k))

theorem rootParameterEquiv_val (K : Type) [Field K] (k : Roots A) (a : Multiplicative K) :
    (rootParameterEquiv A hd hs hp ho K k a).val = selectedRootHom A hd hs hp ho K k a := rfl

theorem rootParameterEquiv_symm_val (K : Type) [Field K] (k : Roots A)
    (x : rootSubgroup A hd hs hp ho K k) :
    selectedRootHom A hd hs hp ho K k ((rootParameterEquiv A hd hs hp ho K k).symm x) = x.val :=
  congrArg Subtype.val ((rootParameterEquiv A hd hs hp ho K k).apply_symm_apply x)

def rootLineInclusion (K : Type) [Field K] (k : Roots A) (hk : ∀ i,0≤k.val i) :
    rootSubgroup A hd hs hp ho K k →* PositiveGroup A hd hs hp ho K :=
  Subgroup.inclusion (positive_root_subgroup_le A hd hs hp ho K k hk)

def rootCoordinatesEquiv (K : Type) [Field K] (h : ℤ) :
    (∀ k : ExactHeightRoot A h,rootSubgroup A hd hs hp ho K k.val.val) ≃*
      (ExactHeightRoot A h → Multiplicative K) :=
  MulEquiv.piCongrRight (fun k => (rootParameterEquiv A hd hs hp ho K k.val.val).symm)

def intrinsicHeightLayerEquiv (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    (∀ k : ExactHeightRoot A h,rootSubgroup A hd hs hp ho K k.val.val) ≃*
      (heightTailInPositive A hd hs hp ho K h).map
        (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1))) :=
  (rootCoordinatesEquiv A hd hs hp ho K h).trans (heightLayerEquiv A hd hs hp ho K h hh)

theorem coordinates_mulSingle (K : Type) [Field K] (h : ℤ)
    (k : ExactHeightRoot A h) (x : rootSubgroup A hd hs hp ho K k.val.val) :
    rootCoordinatesEquiv A hd hs hp ho K h (Pi.mulSingle k x) =
      Pi.mulSingle k ((rootParameterEquiv A hd hs hp ho K k.val.val).symm x) := by
  classical
  funext j
  by_cases hj : j=k
  · subst j
    simp [rootCoordinatesEquiv,MulEquiv.piCongrRight]
  · simp [rootCoordinatesEquiv,MulEquiv.piCongrRight,hj,Ne.symm hj]

theorem intrinsicHeightLayerEquiv_mulSingle (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (k : ExactHeightRoot A h) (x : rootSubgroup A hd hs hp ho K k.val.val) :
    (intrinsicHeightLayerEquiv A hd hs hp ho K h hh (Pi.mulSingle k x)).val =
      (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1)))
        (rootLineInclusion A hd hs hp ho K k.val.val k.val.property x) := by
  classical
  change exactHeightProductHom A hd hs hp ho K h hh
    (rootCoordinatesEquiv A hd hs hp ho K h (Pi.mulSingle k x)) = _
  rw [coordinates_mulSingle,exactHeightProductHom,MonoidHom.noncommPiCoprod_mulSingle]
  change (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1)))
    (positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property
      ((rootParameterEquiv A hd hs hp ho K k.val.val).symm x)) = _
  apply congrArg (QuotientGroup.mk' (heightTailInPositive A hd hs hp ho K (h+1)))
  apply Subtype.ext
  exact rootParameterEquiv_symm_val A hd hs hp ho K k.val.val x

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateIntrinsicHeightLayer
