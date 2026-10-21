import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentCharacteristicLayers
import Mathlib.Algebra.Group.Action.End

/-! Every actual automorphism of U induces an actual additive automorphism
of the original field via the intrinsic centre quotient. The coordinate
intertwining identity retains the original first-coordinate map. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open CFSGSuzukiFieldParameters

theorem centralParameters_map_aut (m : ℕ) (hm : 1≤m) (f : MulAut (unipotentSubgroup m)) :
    (centralParameters m).map f.toMonoidHom=centralParameters m := by
  rw [←center_eq_centralParameters m hm]
  exact Subgroup.characteristic_iff_map_eq.mp inferInstance f

@[simp] theorem firstParameterQuotientEquiv_mk (m : ℕ) (g : unipotentSubgroup m) :
    firstParameterQuotientEquiv m (QuotientGroup.mk' (centralParameters m) g)=
      firstParameterHom m g := rfl

def firstLayerMulAut (m : ℕ) (hm : 1≤m) (f : MulAut (unipotentSubgroup m)) :
    MulAut (Multiplicative (Field m)) :=
  (firstParameterQuotientEquiv m).symm.trans
    ((QuotientGroup.congr (centralParameters m) (centralParameters m) f
      (centralParameters_map_aut m hm f)).trans (firstParameterQuotientEquiv m))

theorem firstLayerMulAut_first (m : ℕ) (hm : 1≤m) (f : MulAut (unipotentSubgroup m))
    (g : unipotentSubgroup m) :
    firstLayerMulAut m hm f (firstParameterHom m g)=firstParameterHom m (f g) := by
  change firstParameterQuotientEquiv m
      (QuotientGroup.congr (centralParameters m) (centralParameters m) f
        (centralParameters_map_aut m hm f)
        ((firstParameterQuotientEquiv m).symm (firstParameterHom m g)))=_
  rw [←firstParameterQuotientEquiv_mk m g,MulEquiv.symm_apply_apply,
    QuotientGroup.congr_mk',firstParameterQuotientEquiv_mk]

def firstLayerAddAut (m : ℕ) (hm : 1≤m) (f : MulAut (unipotentSubgroup m)) :
    AddAut (Field m) where
  toFun x := (firstLayerMulAut m hm f (Multiplicative.ofAdd x)).toAdd
  invFun x := ((firstLayerMulAut m hm f).symm (Multiplicative.ofAdd x)).toAdd
  left_inv x := (firstLayerMulAut m hm f).symm_apply_apply (Multiplicative.ofAdd x)
  right_inv x := (firstLayerMulAut m hm f).apply_symm_apply (Multiplicative.ofAdd x)
  map_add' x y := map_mul (firstLayerMulAut m hm f) (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

/-- Exact intertwining on the actual U, not only cardinal agreement of
an abstract quotient with the field. -/
theorem firstLayerAddAut_first (m : ℕ) (hm : 1≤m) (f : MulAut (unipotentSubgroup m))
    (g : unipotentSubgroup m) :
    firstLayerAddAut m hm f (firstParameter m g)=firstParameter m (f g) :=
  congrArg Multiplicative.toAdd (firstLayerMulAut_first m hm f g)

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
