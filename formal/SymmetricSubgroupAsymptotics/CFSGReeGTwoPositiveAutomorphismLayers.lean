import SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveCharacteristicLayers
import SymmetricSubgroupAsymptotics.CFSGInvariantQuotientAutomorphism

/-! Intrinsic U3 automorphisms act on its three actual additive field
layers. The middle layer uses only the restricted ambient U3 action:
the original centre is not claimed characteristic in the abstract
abelian firstKernel. No ambient group automorphism is lifted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveAutomorphismLayers
open CFSGReeGTwoFieldParameters CFSGReeGTwoOriginalPositiveSubgroup
open CFSGReeGTwoPositiveCentre CFSGReeGTwoPositiveFirstQuotient
open CFSGReeGTwoPositiveDerivedKernel CFSGReeGTwoPositiveCharacteristicLayers

private def restrictAut {L : Type*} [Group L] (S : Subgroup L) (hs : S.Characteristic)
    (f : MulAut L) : MulAut S where
  toFun u := ⟨f u.val,Subgroup.characteristic_iff_le_comap.mp hs f u.property⟩
  invFun u := ⟨f.symm u.val,Subgroup.characteristic_iff_le_comap.mp hs f.symm u.property⟩
  left_inv u := Subtype.ext (f.symm_apply_apply u.val)
  right_inv u := Subtype.ext (f.apply_symm_apply u.val)
  map_mul' u v := Subtype.ext (map_mul f u.val v.val)

private def restrictAutHom {L : Type*} [Group L] (S : Subgroup L) (hs : S.Characteristic) :
    MulAut L →* MulAut S where
  toFun := restrictAut S hs
  map_one' := by apply MulEquiv.ext; intro u; apply Subtype.ext; rfl
  map_mul' a b := by apply MulEquiv.ext; intro u; apply Subtype.ext; rfl

def firstKernelAction (m : ℕ) (hm : 1≤m) :
    MulAut (fixedPositiveGroup m) →* MulAut (firstKernel m) :=
  restrictAutHom (firstKernel m) (firstKernel_characteristic m hm)

theorem firstKernelAction_val (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (u : firstKernel m) : (firstKernelAction m hm f u).val=f u.val := rfl

private theorem firstKernel_invariant (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m)) :
    (firstHom m).ker.map f.toMonoidHom=(firstHom m).ker :=
  Subgroup.characteristic_iff_map_eq.mp (firstKernel_characteristic m hm) f

def firstAction (m : ℕ) (hm : 1≤m) : MulAut (fixedPositiveGroup m) →* AddAut (Field m) :=
  CFSGInvariantQuotientAutomorphism.quotientAddAutHom (firstHom m) (firstHom_surjective m)
    (MonoidHom.id _) (firstKernel_invariant m hm)

theorem firstAction_coordinate (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (u : fixedPositiveGroup m) :
    firstAction m hm f (coordinates m u 0)=coordinates m (f u) 0 :=
  CFSGInvariantQuotientAutomorphism.quotientAddAut_first (firstHom m) (firstHom_surjective m)
    (MonoidHom.id _) (firstKernel_invariant m hm) f u

theorem middleKernel_invariant (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m)) :
    (middleHom m).ker.map (firstKernelAction m hm f).toMonoidHom=(middleHom m).ker := by
  have hc : (Subgroup.center (fixedPositiveGroup m)).map f.toMonoidHom=
      Subgroup.center (fixedPositiveGroup m) := Subgroup.characteristic_iff_map_eq.mp inferInstance f
  ext u
  rw [Subgroup.mem_map_equiv]
  simp only [middleKer_eq_centerInFirst]
  change f.symm u.val∈Subgroup.center (fixedPositiveGroup m) ↔ u.val∈Subgroup.center (fixedPositiveGroup m)
  rw [←Subgroup.mem_map_equiv (f := f),hc]

def middleAction (m : ℕ) (hm : 1≤m) : MulAut (fixedPositiveGroup m) →* AddAut (Field m) :=
  CFSGInvariantQuotientAutomorphism.quotientAddAutHom (middleHom m) (middleHom_surjective m)
    (firstKernelAction m hm) (middleKernel_invariant m hm)

theorem middleAction_coordinate (m : ℕ) (hm : 1≤m) (f : MulAut (fixedPositiveGroup m))
    (u : firstKernel m) :
    middleAction m hm f (coordinates m u.val 1)=coordinates m (f u.val) 1 :=
  CFSGInvariantQuotientAutomorphism.quotientAddAut_first (middleHom m) (middleHom_surjective m)
    (firstKernelAction m hm) (middleKernel_invariant m hm) f u

def centralEquiv (m : ℕ) : Multiplicative (Field m) ≃* Subgroup.center (fixedPositiveGroup m) :=
  (MonoidHom.ofInjective (centralHom_injective m)).trans (MulEquiv.subgroupCongr (centralHom_range m))

theorem centralEquiv_val (m : ℕ) (d : Multiplicative (Field m)) :
    (centralEquiv m d).val=centralHom m d := rfl

private def multiplicativeAutToAdd {K : Type*} [AddCommGroup K]
    (f : MulAut (Multiplicative K)) : AddAut K where
  toFun x := (f (Multiplicative.ofAdd x)).toAdd
  invFun x := (f.symm (Multiplicative.ofAdd x)).toAdd
  left_inv x := f.symm_apply_apply (Multiplicative.ofAdd x)
  right_inv x := f.apply_symm_apply (Multiplicative.ofAdd x)
  map_add' x y := map_mul f (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

private def multiplicativeAutToAddHom {K : Type*} [AddCommGroup K] :
    MulAut (Multiplicative K) →* AddAut K where
  toFun := multiplicativeAutToAdd
  map_one' := by apply AddEquiv.ext; intro x; rfl
  map_mul' a b := by apply AddEquiv.ext; intro x; rfl

private def centralMulAction (m : ℕ) :
    MulAut (fixedPositiveGroup m) →* MulAut (Multiplicative (Field m)) :=
  (MulAut.congr (centralEquiv m).symm).toMonoidHom.comp
    (restrictAutHom (Subgroup.center (fixedPositiveGroup m)) inferInstance)

def centralAction (m : ℕ) : MulAut (fixedPositiveGroup m) →* AddAut (Field m) :=
  multiplicativeAutToAddHom.comp (centralMulAction m)

theorem centralAction_intertwine (m : ℕ) (f : MulAut (fixedPositiveGroup m)) (d : Field m) :
    f (centralHom m (Multiplicative.ofAdd d))=
      centralHom m (Multiplicative.ofAdd (centralAction m f d)) := by
  have he := congrArg (fun z : Subgroup.center (fixedPositiveGroup m) => z.val)
    ((centralEquiv m).apply_symm_apply
      (restrictAut (Subgroup.center (fixedPositiveGroup m)) inferInstance f
        (centralEquiv m (Multiplicative.ofAdd d))))
  exact he.symm

end SymmetricSubgroupAsymptotics.CFSGReeGTwoPositiveAutomorphismLayers
