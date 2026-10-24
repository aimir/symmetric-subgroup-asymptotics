import SymmetricSubgroupAsymptotics.CFSGE6GeckHeightTorusAutomorphism
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightLayerCoordinates

/-! Every actual E6 exact-height coordinate transforms by its literal
root character under the genuine product torus. The equality is checked
on one-coordinate root inclusions and then extended by the Pi universal
property; there is no coordinate-action hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckHeightTorusCoordinates
open CFSGE6GeckHeightTorusAutomorphism CFSGE6GeckProductTorusRootAction
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckHeightQuotientTwist
open CFSGNormTwoCoordinateHeightLayerCoordinates CFSGNormTwoCoordinateExactHeightLayer
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateSelectedRootElement CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (CFSGNormTwoRootPairing.Roots A) := Classical.decEq _
local instance tailNormal (K : Type) [Field K] (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive A hd hs hp ho K h

abbrev ScalarCoordinates (K : Type) (h : ℤ) := ExactHeightRoot A h→Multiplicative K

def coordinateTorus (K : Type) [Field K] (x : Fin 6→Kˣ) (h : ℤ) :
    ScalarCoordinates K h→*ScalarCoordinates K h where
  toFun c k := Multiplicative.ofAdd ((rootCharacter K x k.val.val : K)*(c k).toAdd)
  map_one' := by
    funext k
    change Multiplicative.ofAdd ((rootCharacter K x k.val.val : K)*0)=1
    rw [mul_zero]
    rfl
  map_mul' c d := by
    funext k
    change Multiplicative.ofAdd ((rootCharacter K x k.val.val : K)*((c k).toAdd+(d k).toAdd))=
      Multiplicative.ofAdd ((rootCharacter K x k.val.val : K)*(c k).toAdd+
        (rootCharacter K x k.val.val : K)*(d k).toAdd)
    rw [mul_add]

private theorem coordinateTorus_mulSingle (K : Type) [Field K] (x : Fin 6→Kˣ)
    (h : ℤ) (k : ExactHeightRoot A h) (a : Multiplicative K) :
    coordinateTorus K x h (Pi.mulSingle k a)=
      Pi.mulSingle k (Multiplicative.ofAdd ((rootCharacter K x k.val.val : K)*a.toAdd)) := by
  funext j
  by_cases hj : j=k
  · subst j
    simp only [coordinateTorus,MonoidHom.coe_mk,OneHom.coe_mk,Pi.mulSingle_eq_same]
  · simp only [coordinateTorus,MonoidHom.coe_mk,OneHom.coe_mk,Pi.mulSingle_eq_of_ne hj,
      toAdd_one,mul_zero,ofAdd_zero]

private theorem heightLayer_mulSingle (K : Type) [Field K] (h : ℤ) (hh : 0<h)
    (k : ExactHeightRoot A h) (a : Multiplicative K) :
    (heightLayerEquiv A hd hs hp ho K h hh (Pi.mulSingle k a)).val=
      quotientRootHom A hd hs hp ho K h k.val.val k.val.property a := by
  change exactHeightProductHom A hd hs hp ho K h hh (Pi.mulSingle k a)=_
  exact MonoidHom.noncommPiCoprod_mulSingle
    (fun l : ExactHeightRoot A h=>quotientRootHom A hd hs hp ho K h l.val.val l.val.property) k a

private theorem quotientTorus_root (K : Type) [Field K] [Finite K]
    (x : Fin 6→Kˣ) (h : ℤ) (k : ExactHeightRoot A h) (a : Multiplicative K) :
    quotientTorus K x h (quotientRootHom A hd hs hp ho K h k.val.val k.val.property a)=
      quotientRootHom A hd hs hp ho K h k.val.val k.val.property
        (Multiplicative.ofAdd ((rootCharacter K x k.val.val : K)*a.toAdd)) := by
  change quotientTorus K x h
    (QuotientGroup.mk' (TailInPositive K (h+1))
      (positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property a))=_
  rw [quotientTorus_mk]
  apply congrArg (QuotientGroup.mk' (TailInPositive K (h+1)))
  apply Subtype.ext
  change CFSGE6GeckProductTorus.rawProductTorus K x*rawSelectedRoot K k.val.val a.toAdd*
    (CFSGE6GeckProductTorus.rawProductTorus K x)⁻¹=
      rawSelectedRoot K k.val.val ((rootCharacter K x k.val.val : K)*a.toAdd)
  simpa only [mul_comm] using product_torus_selected_root_action K x k.val.val a.toAdd

theorem quotient_coordinate_intertwining (K : Type) [Field K] [Finite K]
    (x : Fin 6→Kˣ) (h : ℤ) (hh : 0<h) (c : ScalarCoordinates K h) :
    quotientTorus K x h (heightLayerEquiv A hd hs hp ho K h hh c).val=
      (heightLayerEquiv A hd hs hp ho K h hh (coordinateTorus K x h c)).val := by
  let e := heightLayerEquiv A hd hs hp ho K h hh
  let C := ((TailInPositive K h).map (QuotientGroup.mk' (TailInPositive K (h+1)))).subtype
  have he : (quotientTorus K x h).toMonoidHom.comp (C.comp e.toMonoidHom)=
      (C.comp e.toMonoidHom).comp (coordinateTorus K x h) := by
    apply MonoidHom.pi_ext
    intro k a
    change quotientTorus K x h (heightLayerEquiv A hd hs hp ho K h hh (Pi.mulSingle k a)).val=
      (heightLayerEquiv A hd hs hp ho K h hh (coordinateTorus K x h (Pi.mulSingle k a))).val
    rw [coordinateTorus_mulSingle,heightLayer_mulSingle,heightLayer_mulSingle]
    exact quotientTorus_root K x h k a
  exact DFunLike.congr_fun he c

end SymmetricSubgroupAsymptotics.CFSGE6GeckHeightTorusCoordinates
