import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalRootCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedRootAction
import SymmetricSubgroupAsymptotics.CFSGSubgroupFamilyStabilizer
import SymmetricSubgroupAsymptotics.CFSGInvariantSubgroupCoordinateImage

/-! Actual restrictions of pair-preserving ORIGINAL Ree automorphisms.
Intrinsic root-label recovery supplies the invariant subgroups, and the
proved original coordinate equivalences supply the additive outer and
Suzuki middle actions. No quotient automorphism is lifted to a source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalRootCoordinates
open CFSGReeFFourOriginalRootIntersections CFSGReeFFourOriginalSignedRootAction
open CFSGReeFFourOriginalRootAction CFSGReeFFourOriginalPositiveSylow
open CFSGReeFFourOriginalOppositeAlignment CFSGReeFFourOuterTorusAction
open CFSGSubgroupFamilyStabilizer CFSGInvariantSubgroupCoordinateImage

def pairStabilizer (m : ℕ) (hm : 0<m) : Subgroup (MulAut (CFSG.Models.ReeF4 m)) :=
  familyStabilizer (fun neg : Bool=>if neg then originalNegative m hm
    else (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)))

theorem pair_preserves_positive (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) :
    (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)).map f.val.toMonoidHom=
      (reePositiveSylow m hm : Subgroup (CFSG.Models.ReeF4 m)) := f.property false

theorem pair_preserves_negative (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) :
    (originalNegative m hm).map f.val.toMonoidHom=originalNegative m hm := f.property true

theorem pair_preserves_signed_block (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) (neg b : Bool) :
    (originalSignedRootBlock m hm neg b).map f.val.toMonoidHom=originalSignedRootBlock m hm neg b :=
  original_signed_root_block_map_eq m hm f.val
    (pair_preserves_positive m hm f) (pair_preserves_negative m hm f) neg b

def rootBlockRestriction (m : ℕ) (hm : 0<m) (b : Bool) :
    pairStabilizer m hm →* MulAut (originalRootBlock m hm b) where
  toFun f := restrictAut (originalRootBlock m hm b) f.val
    (original_root_block_map_eq m hm f.val
      (pair_preserves_positive m hm f) (pair_preserves_negative m hm f) b)
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  map_mul' f g := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl

theorem rootBlockRestriction_val (m : ℕ) (hm : 0<m) (b : Bool)
    (f : pairStabilizer m hm) (x : originalRootBlock m hm b) :
    (rootBlockRestriction m hm b f x).val=f.val x.val := rfl

def outerMulRestriction (m : ℕ) (hm : 0<m) :
    pairStabilizer m hm →* MulAut (Multiplicative (Field m)) :=
  (MulAut.congr (originalOuterEquiv m hm).symm).toMonoidHom.comp
    (rootBlockRestriction m hm false)

theorem outerMulRestriction_intertwines (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) (a : Multiplicative (Field m)) :
    originalOuterHom m hm (outerMulRestriction m hm f a)=f.val (originalOuterHom m hm a) := by
  have he := (originalOuterEquiv m hm).apply_symm_apply
    (rootBlockRestriction m hm false f (originalOuterEquiv m hm a))
  change originalOuterEquiv m hm (outerMulRestriction m hm f a)=
    rootBlockRestriction m hm false f (originalOuterEquiv m hm a) at he
  have hv := congrArg (fun x : originalRootBlock m hm false=>x.val) he
  simpa only [originalOuterEquiv_val,rootBlockRestriction_val] using hv

private def additiveAut {K : Type*} [AddGroup K] (e : MulAut (Multiplicative K)) : AddAut K where
  toFun a := (e (Multiplicative.ofAdd a)).toAdd
  invFun a := (e.symm (Multiplicative.ofAdd a)).toAdd
  left_inv a := congrArg (fun z : Multiplicative K=>z.toAdd) (e.symm_apply_apply (Multiplicative.ofAdd a))
  right_inv a := congrArg (fun z : Multiplicative K=>z.toAdd) (e.apply_symm_apply (Multiplicative.ofAdd a))
  map_add' a b := congrArg (fun z : Multiplicative K=>z.toAdd)
    (map_mul e (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

private def additiveAutHom {K : Type*} [AddGroup K] :
    MulAut (Multiplicative K) →* AddAut K where
  toFun := additiveAut
  map_one' := by
    apply AddEquiv.ext
    intro a
    rfl
  map_mul' f g := by
    apply AddEquiv.ext
    intro a
    rfl

def outerRestriction (m : ℕ) (hm : 0<m) : pairStabilizer m hm →* AddAut (Field m) :=
  (additiveAutHom (K := Field m)).comp (outerMulRestriction m hm)

theorem outerRestriction_apply (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) (a : Field m) :
    outerRestriction m hm f a=(outerMulRestriction m hm f (Multiplicative.ofAdd a)).toAdd := rfl

theorem outerRestriction_intertwines (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) (a : Field m) :
    originalOuterHom m hm (Multiplicative.ofAdd (outerRestriction m hm f a))=
      f.val (originalOuterHom m hm (Multiplicative.ofAdd a)) :=
  outerMulRestriction_intertwines m hm f (Multiplicative.ofAdd a)

def middleRestriction (m : ℕ) (hm : 0<m) :
    pairStabilizer m hm →* MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m) :=
  (MulAut.congr (originalMiddleSuzukiEquiv m hm)).toMonoidHom.comp
    (rootBlockRestriction m hm true)

private theorem congrAutHom_apply {G H P : Type*} [Group G] [Group H] [Monoid P]
    (e : G ≃* H) (h : P →* MulAut G) (f : P) (x : G) :
    ((MulAut.congr e).toMonoidHom.comp h) f (e x)=e (h f x) := by
  change e (h f (e.symm (e x)))=e (h f x)
  rw [e.symm_apply_apply]

theorem middleRestriction_intertwines (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) (x : originalRootBlock m hm true) :
    middleRestriction m hm f (originalMiddleSuzukiEquiv m hm x)=
      originalMiddleSuzukiEquiv m hm (rootBlockRestriction m hm true f x) :=
  congrAutHom_apply (originalMiddleSuzukiEquiv m hm)
    (rootBlockRestriction m hm true) f x

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairRestriction
