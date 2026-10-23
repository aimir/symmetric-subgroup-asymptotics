import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckIntrinsicHeightAction
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedHeightOrbitLifting
import Mathlib.GroupTheory.Index

/-! Upper cardinal recursion for actual fixed E6 height tails.
The coordinate map is retained with its exact next-tail kernel; only an
upper bound on its range is used, with no fixed-point surjectivity input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedTailCardinality
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckHeightQuotientTwist
open CFSGTwistedE6GeckIntrinsicHeightAction CFSGTwistedE6GeckHeightRootPermutation
open CFSGTwistedE6GeckFixedHeightOrbitLifting
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGNormTwoCoordinateRootHeightFiltration

variable (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)

local instance tailNormal (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos K h

def fixedPositive : Subgroup (Positive K) :=
  (positiveTwist K sigma).toMonoidHom.eqLocus (MonoidHom.id _)

def heightProjection (h : ℤ) : TailInPositive K h→*HeightImage K h :=
  (QuotientGroup.mk' (TailInPositive K (h+1))).subgroupMap (TailInPositive K h)

def fixedTail (h : ℤ) : Subgroup (Positive K) :=
  TailInPositive K h ⊓ fixedPositive K sigma

def fixedCoordinates (h : ℤ) : Subgroup (RootCoordinates K h) :=
  (coordinateTwist K sigma h).toMonoidHom.eqLocus (MonoidHom.id _)

private theorem fixed_image (h : ℤ) (u : fixedTail K sigma h) :
    heightImageTwist K sigma h
      (heightProjection K h ⟨u.val,u.property.1⟩) =
        heightProjection K h ⟨u.val,u.property.1⟩ := by
  apply Subtype.ext
  change quotientTwist K sigma h (QuotientGroup.mk' (TailInPositive K (h+1)) u.val) =
    QuotientGroup.mk' (TailInPositive K (h+1)) u.val
  rw [quotientTwist_mk]
  exact congrArg (QuotientGroup.mk' (TailInPositive K (h+1))) u.property.2

private theorem fixed_symm {C Q:Type*} [Group C] [Group Q]
    (e:C≃*Q) (F:MulAut C) (T:MulAut Q)
    (h:∀c,T (e c)=e (F c)) (x:Q) (hx:T x=x) : F (e.symm x)=e.symm x := by
  apply e.injective
  rw [←h,MulEquiv.apply_symm_apply,hx]

private def underlyingCoordinateHom (h:ℤ) (hh:0<h) :
    fixedTail K sigma h→*RootCoordinates K h :=
  ((intrinsicCoordinates K h hh).symm.toMonoidHom.comp (heightProjection K h)).comp
    (Subgroup.inclusion (show fixedTail K sigma h≤TailInPositive K h from inf_le_left))

private theorem underlyingCoordinateHom_fixed (h:ℤ) (hh:0<h) (u:fixedTail K sigma h) :
    underlyingCoordinateHom K sigma h hh u∈fixedCoordinates K sigma h := by
  change coordinateTwist K sigma h ((intrinsicCoordinates K h hh).symm
    (heightProjection K h ⟨u.val,u.property.1⟩))=
      (intrinsicCoordinates K h hh).symm (heightProjection K h ⟨u.val,u.property.1⟩)
  exact fixed_symm (intrinsicCoordinates K h hh) (coordinateTwist K sigma h)
    (heightImageTwist K sigma h) (coordinate_intertwining K sigma h hh) _ (fixed_image K sigma h u)

def coordinateHom (h : ℤ) (hh : 0 < h) :
    fixedTail K sigma h →* fixedCoordinates K sigma h :=
  (underlyingCoordinateHom K sigma h hh).codRestrict (fixedCoordinates K sigma h)
    (underlyingCoordinateHom_fixed K sigma h hh)

theorem coordinateHom_apply (h : ℤ) (hh : 0 < h) (u : fixedTail K sigma h) :
    (coordinateHom K sigma h hh u).val =
      (intrinsicCoordinates K h hh).symm (heightProjection K h ⟨u.val,u.property.1⟩) := rfl

private theorem symm_eq_one_iff {C Q : Type*} [Group C] [Group Q]
    (S : Subgroup Q) (e : C ≃* S) (x : S) : e.symm x = 1 ↔ x.val = 1 := by
  constructor
  · intro he
    have hh := congrArg e he
    have hx : x = 1 := by simpa only [MulEquiv.apply_symm_apply,map_one] using hh
    exact congrArg Subtype.val hx
  · intro he
    have hx : x = 1 := Subtype.ext he
    rw [hx,map_one]

theorem coordinateHom_eq_one_iff (h : ℤ) (hh : 0 < h) (u : fixedTail K sigma h) :
    coordinateHom K sigma h hh u = 1 ↔ u.val ∈ TailInPositive K (h+1) := by
  calc
    coordinateHom K sigma h hh u = 1 ↔ (coordinateHom K sigma h hh u).val = 1 :=
      Subtype.ext_iff
    _ ↔ (heightProjection K h ⟨u.val,u.property.1⟩).val = 1 := by
      rw [coordinateHom_apply]
      exact symm_eq_one_iff (HeightImage K h) (intrinsicCoordinates K h hh) _
    _ ↔ u.val ∈ TailInPositive K (h+1) :=
      @QuotientGroup.eq_one_iff (Positive K) inferInstance (TailInPositive K (h+1))
        (heightTail_normal_in_positive CartanMatrix.E₆ CartanMatrix.E₆_diag
          CartanMatrix.E₆_transpose E6_positive_definite
          CartanMatrix.E₆_off_diag_nonpos K (h+1)) u.val

omit [Finite K] in
private theorem next_le (h : ℤ) : fixedTail K sigma (h+1) ≤ fixedTail K sigma h := by
  intro u hu
  refine ⟨?_,hu.2⟩
  exact heightTail_antitone CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite
    CartanMatrix.E₆_off_diag_nonpos K (by omega : h ≤ h+1) hu.1

def kernelEquiv (h : ℤ) (hh : 0 < h) :
    (coordinateHom K sigma h hh).ker ≃* fixedTail K sigma (h+1) where
  toFun u := ⟨u.val.val,
    (coordinateHom_eq_one_iff K sigma h hh u.val).mp u.property,u.val.property.2⟩
  invFun v := ⟨⟨v.val,next_le K sigma h v.property⟩,
    (coordinateHom_eq_one_iff K sigma h hh _).mpr v.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem fixedTail_card_sq_step (h : ℤ) (hh : 0 < h) :
    Nat.card (fixedTail K sigma h)^2≤
      Nat.card (fixedCoordinates K sigma h)^2*Nat.card (fixedTail K sigma (h+1))^2 := by
  let f := coordinateHom K sigma h hh
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hc
  rw [Nat.card_congr (kernelEquiv K sigma h hh).toEquiv] at hc
  have hr : Nat.card f.range≤Nat.card (fixedCoordinates K sigma h) :=
    Nat.card_le_card_of_injective (fun x:f.range=>x.val) Subtype.val_injective
  calc
    Nat.card (fixedTail K sigma h)^2=
        (Nat.card (fixedTail K sigma (h+1))*Nat.card f.range)^2 := by rw [hc]
    _≤(Nat.card (fixedTail K sigma (h+1))*Nat.card (fixedCoordinates K sigma h))^2 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hr) 2
    _=Nat.card (fixedCoordinates K sigma h)^2*Nat.card (fixedTail K sigma (h+1))^2 := by ring

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedTailCardinality
