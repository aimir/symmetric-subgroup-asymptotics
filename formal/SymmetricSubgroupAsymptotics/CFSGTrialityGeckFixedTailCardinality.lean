import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveGeneration
import Mathlib.GroupTheory.Index

/-! Exact cardinal recursion for the ACTUAL triality-fixed height tails.
The coordinate hom is surjective because the proved section representative
is genuinely fixed. No exactness of fixed points is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedTailCardinality
open CFSGTrialityD4NormTwo CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckFixedPositiveGeneration CFSGTrialityGeckFixedHeightClassLifting
open CFSGTrialityGeckWordHeightCoordinates CFSGTrialityGeckWordCoordinateTwist
open CFSGTrialityGeckHeightCoordinateAction CFSGTrialityGeckHeightQuotientTwist
open CFSGTrialityGeckWordRootIndex CFSGNormTwoCoordinateRootHeightFiltration

variable (K : Type) [Field K] [Finite K] (sigma : K ≃+* K)

local instance tailNormal (h : ℤ) : (TailInPositive K h).Normal :=
  heightTail_normal_in_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K h

def fixedTail (h : ℤ) : Subgroup (Positive K) :=
  TailInPositive K h ⊓ fixedPositive K sigma

def fixedCoordinates (h : ℤ) : Subgroup (WordHeightIndex h → Multiplicative K) :=
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

def coordinateHom (h : ℤ) (hh : 0 < h) :
    fixedTail K sigma h →* fixedCoordinates K sigma h :=
  (((wordHeightLayerEquiv K h hh).symm.toMonoidHom.comp (heightProjection K h)).comp
    (Subgroup.inclusion (show fixedTail K sigma h ≤ TailInPositive K h from inf_le_left))).codRestrict
      (fixedCoordinates K sigma h) (fun u => by
        apply (fixed_iff_coordinates K sigma h hh _).mp
        change heightImageTwist K sigma h
          (wordHeightLayerEquiv K h hh ((wordHeightLayerEquiv K h hh).symm
            (heightProjection K h ⟨u.val,u.property.1⟩))) =
          wordHeightLayerEquiv K h hh ((wordHeightLayerEquiv K h hh).symm
            (heightProjection K h ⟨u.val,u.property.1⟩))
        rw [MulEquiv.apply_symm_apply]
        exact fixed_image K sigma h u)

theorem coordinateHom_apply (h : ℤ) (hh : 0 < h) (u : fixedTail K sigma h) :
    (coordinateHom K sigma h hh u).val =
      (wordHeightLayerEquiv K h hh).symm (heightProjection K h ⟨u.val,u.property.1⟩) := rfl

theorem coordinateHom_surjective (h : ℤ) (hh : 0 < h) :
    Function.Surjective (coordinateHom K sigma h hh) := by
  intro c
  let p := sectionRepresentative K sigma h c.val
  let u : fixedTail K sigma h := ⟨p.val,p.property,
    sectionRepresentative_fixed K sigma h c.val c.property⟩
  refine ⟨u,?_⟩
  apply Subtype.ext
  rw [coordinateHom_apply]
  change (wordHeightLayerEquiv K h hh).symm (heightProjection K h p) = c.val
  rw [sectionRepresentative_image K sigma h hh c.val c.property,
    MulEquiv.symm_apply_apply]

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
      exact symm_eq_one_iff (HeightImage K h) (wordHeightLayerEquiv K h hh) _
    _ ↔ u.val ∈ TailInPositive K (h+1) :=
      @QuotientGroup.eq_one_iff (Positive K) inferInstance (TailInPositive K (h+1))
        (heightTail_normal_in_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
          (CartanMatrix.D_transpose 4) D4_positive_definite
          (CartanMatrix.D_off_diag_nonpos 4) K (h+1)) u.val

private theorem next_le (h : ℤ) : fixedTail K sigma (h+1) ≤ fixedTail K sigma h := by
  intro u hu
  refine ⟨?_,hu.2⟩
  exact heightTail_antitone (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite
    (CartanMatrix.D_off_diag_nonpos 4) K (by omega : h ≤ h+1) hu.1

def kernelEquiv (h : ℤ) (hh : 0 < h) :
    (coordinateHom K sigma h hh).ker ≃* fixedTail K sigma (h+1) where
  toFun u := ⟨u.val.val,
    (coordinateHom_eq_one_iff K sigma h hh u.val).mp u.property,u.val.property.2⟩
  invFun v := ⟨⟨v.val,next_le K sigma h v.property⟩,
    (coordinateHom_eq_one_iff K sigma h hh _).mpr v.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem fixedTail_card_step (h : ℤ) (hh : 0 < h) :
    Nat.card (fixedTail K sigma h) =
      Nat.card (fixedCoordinates K sigma h) * Nat.card (fixedTail K sigma (h+1)) := by
  let f := coordinateHom K sigma h hh
  have hc := f.ker.card_mul_index
  rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr (coordinateHom_surjective K sigma h hh),
    Subgroup.card_top] at hc
  rw [Nat.card_congr (kernelEquiv K sigma h hh).toEquiv] at hc
  exact hc.symm.trans (Nat.mul_comm _ _)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedTailCardinality
