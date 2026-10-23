import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedTailCardinality
import SymmetricSubgroupAsymptotics.CFSGFiniteInvolutionCoordinatesCardinality
import Mathlib.Data.Fintype.EquivFin

/-! An upper cardinal bound on actual fixed E6 exact-height coordinates.
A singleton root transport may have a sign; injectivity alone suffices.
No assertion identifies all singleton fixed parameters with K. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedCoordinateCardinality
open CFSGE6GeckFixedTailCardinality CFSGTwistedE6GeckIntrinsicHeightAction
open CFSGTwistedE6GeckHeightRootPermutation CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateAllRootParameters CFSGExceptionalCartanPositiveDefinite

local instance indexOrder (h:ℤ) : LinearOrder (HeightIndex h) :=
  LinearOrder.lift' (Fintype.equivFin (HeightIndex h)) (Fintype.equivFin (HeightIndex h)).injective

private theorem coordinate_fixed_iff (K:Type) [Field K] [Finite K]
    (sigma:K≃+*K) (h:ℤ) (hh:0<h) (c:RootCoordinates K h) :
    coordinateTwist K sigma h c=c↔
      ∀k,rootLineTwist K sigma h k (c k)=c (heightRootPermutation h k) := by
  calc
    coordinateTwist K sigma h c=c↔
        intrinsicCoordinates K h hh (coordinateTwist K sigma h c)=intrinsicCoordinates K h hh c :=
      (intrinsicCoordinates K h hh).injective.eq_iff.symm
    _↔heightImageTwist K sigma h (intrinsicCoordinates K h hh c)=intrinsicCoordinates K h hh c := by
      rw [coordinate_intertwining]
    _↔_ := fixed_iff_coordinates K sigma h hh c

private def fixedCoordinatesEquiv (K:Type) [Field K] [Finite K]
    (sigma:K≃+*K) (h:ℤ) (hh:0<h) :
    fixedCoordinates K sigma h≃
      CFSGFiniteInvolutionCoordinatesCardinality.fixedCoordinates
        (fun k:HeightIndex h=>rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag
          CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val)
        (heightRootPermutation h) (fun k=>rootLineTwist K sigma h k) where
  toFun c:=⟨c.val,(coordinate_fixed_iff K sigma h hh c.val).mp c.property⟩
  invFun c:=⟨c.val,(coordinate_fixed_iff K sigma h hh c.val).mpr c.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem fixedCoordinates_card_sq_le (K:Type) [Field K] [Finite K]
    (sigma:K≃+*K) (h:ℤ) (hh:0<h) :
    Nat.card (fixedCoordinates K sigma h)^2≤
      Nat.card K^(Nat.card (HeightIndex h)+Nat.card {k:HeightIndex h // heightRootPermutation h k=k}) := by
  rw [Nat.card_congr (fixedCoordinatesEquiv K sigma h hh)]
  exact CFSGFiniteInvolutionCoordinatesCardinality.fixedCoordinates_card_sq_le
    (fun k:HeightIndex h=>rootSubgroup CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val)
    (heightRootPermutation h) (heightRootMap_involutive h)
    (fun k=>rootLineTwist K sigma h k) (fun k=>(rootLineTwist K sigma h k).injective)
    (Nat.card K) (fun k=>rootSubgroup_card CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K k.val.val)

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedCoordinateCardinality
