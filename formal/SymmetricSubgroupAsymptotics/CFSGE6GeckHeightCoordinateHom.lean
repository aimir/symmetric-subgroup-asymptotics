import SymmetricSubgroupAsymptotics.CFSGE6GeckHeightTorusCoordinates
import SymmetricSubgroupAsymptotics.CFSGEquivCoordinateTransport

/-! A genuine coordinate homomorphism on each positive E6 height tail,
with its proved next-tail kernel containment and pointwise torus action.
Coordinates are packaged as one additive vector for finite averaging. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckHeightCoordinateHom
open CFSGE6GeckHeightTorusCoordinates CFSGE6GeckHeightTorusAutomorphism
open CFSGE6GeckProductTorusRootAction CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckHeightQuotientTwist CFSGNormTwoCoordinateHeightLayerCoordinates
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateRootHeightFiltration
open CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance tailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive A hd hs hp ho K h

def piMultiplicative (I K : Type*) [AddGroup K] :
    (I→Multiplicative K)≃*Multiplicative (I→K) where
  toFun c := Multiplicative.ofAdd (fun k=>(c k).toAdd)
  invFun c k := Multiplicative.ofAdd (c.toAdd k)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def projection (K : Type) [Field K] (h : ℤ) :
    TailInPositive K h→*(TailInPositive K h).map (QuotientGroup.mk' (TailInPositive K (h+1))) :=
  (QuotientGroup.mk' (TailInPositive K (h+1))).subgroupMap (TailInPositive K h)

def coordinateHom (K : Type) [Field K] (h : ℤ) (hh : 0<h) :
    TailInPositive K h→*Multiplicative (ExactHeightRoot A h→K) :=
  (piMultiplicative (ExactHeightRoot A h) K).toMonoidHom.comp
    ((heightLayerEquiv A hd hs hp ho K h hh).symm.toMonoidHom.comp (projection K h))

theorem coordinateHom_eq_one_iff (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (u : TailInPositive K h) :
    coordinateHom K h hh u=1 ↔ u.val∈TailInPositive K (h+1) := by
  change (piMultiplicative (ExactHeightRoot A h) K)
    ((heightLayerEquiv A hd hs hp ho K h hh).symm (projection K h u))=1 ↔ _
  rw [CFSGEquivCoordinateTransport.composite_eq_one_iff]
  have he : projection K h u=1 ↔
      QuotientGroup.mk' (TailInPositive K (h+1)) u.val=1 := by
    constructor
    · intro hp'
      exact congrArg Subtype.val hp'
    · intro hq
      exact Subtype.ext hq
  exact he.trans (QuotientGroup.eq_one_iff u.val)

theorem coordinateHom_torus (K : Type) [Field K] [Finite K]
    (x : Fin 6→Kˣ) (h : ℤ) (hh : 0<h) (u v : TailInPositive K h)
    (hv : v.val=positiveTorus K x u.val) (k : ExactHeightRoot A h) :
    (coordinateHom K h hh v).toAdd k=
      (rootCharacter K x k.val.val : K)*(coordinateHom K h hh u).toAdd k := by
  let e := heightLayerEquiv A hd hs hp ho K h hh
  let inc := ((TailInPositive K h).map (QuotientGroup.mk' (TailInPositive K (h+1)))).subtype
  have hv' : inc (projection K h v)=quotientTorus K x h (inc (projection K h u)) := by
    change QuotientGroup.mk' (TailInPositive K (h+1)) v.val=
      quotientTorus K x h (QuotientGroup.mk' (TailInPositive K (h+1)) u.val)
    rw [quotientTorus_mk,hv]
  have hcoord := CFSGEquivCoordinateTransport.coordinates_of_underlying_intertwining
    e inc Subtype.val_injective (quotientTorus K x h) (coordinateTorus K x h)
    (quotient_coordinate_intertwining K x h hh) (projection K h u) (projection K h v) hv'

  exact congrArg (fun c : ScalarCoordinates K h=>(c k).toAdd) hcoord

end SymmetricSubgroupAsymptotics.CFSGE6GeckHeightCoordinateHom
