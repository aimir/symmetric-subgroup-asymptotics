import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterNegativeOne
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterWeylCoset
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterSemilinear

/-! The normalized original outer Weyl element is fixed, and the same
field map acts on both signed outer parameters. This uses the genuine
negative-one constraint, not faithfulness of positive restrictions. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedOuterField
open CFSGReeFFourOriginalOuterNegativeOne CFSGReeFFourOriginalNegativeOuterCoordinates
open CFSGReeFFourOuterSignedConjugation CFSGReeFFourOuterTorusReflection
open CFSGReeFFourOuterFixedRoot CFSGReeFFourOuterUnipotentGeneration
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourPerfectProjection CFSGReeFFourOuterTorusAction
open CFSGReeFFourOriginalOuterWeylCoset CFSGReeFFourOriginalDiagonalNormalizer
open CFSGReeFFourMinimalParabolics CFSGReeFFourFixedBruhatCover
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalOuterSemilinear
open CFSGReeFFourOriginalSignedRootAction

private theorem map_conjugation {G H : Type*} [Group G] [Group H] (F : G→*H) (w x : G) :
    F (w*x*w⁻¹)=F w*F x*(F w)⁻¹ := by rw [map_mul,map_mul,map_inv]

private theorem map_triple_eq {G H : Type*} [Group G] [Group H] (F : G→*H)
    (x y w : G) (he : x*y*x=w) : F x*F y*F x=F w := by rw [←map_mul,←map_mul,he]

private theorem triple_fixed {G : Type*} [Group G] (F : G→*G) (x y : G)
    (hx : F x=x) (hy : F y=y) : F (x*y*x)=x*y*x := by rw [map_mul,map_mul,hx,hy]

private theorem conjugate_eq {G : Type*} [Group G] (w : G) {x y : G} (he : x=y) :
    w*x*w⁻¹=w*y*w⁻¹ := congrArg (fun z=>w*z*w⁻¹) he

private theorem map_conjugate_fixed {G : Type*} [Group G] (F : G→*G) (w x : G)
    (hw : F w=w) : F (w*x*w⁻¹)=w*F x*w⁻¹ := by rw [map_mul,map_mul,map_inv,hw]

theorem originalOuterWeyl_projection (m : ℕ) (hm : 0<m) :
    originalOuterWeyl m hm=fixedToOriginal m hm (outerFixedReflection m) :=
  congrArg (fixedToOriginal m hm) ((simpleWeyl_false m).trans rfl)

theorem original_outer_weyl_word (m : ℕ) (hm : 0<m) :
    originalOuterHom m hm (Multiplicative.ofAdd 1)*
      originalNegativeOuterHom m hm (Multiplicative.ofAdd (-1))*
        originalOuterHom m hm (Multiplicative.ofAdd 1)=originalOuterWeyl m hm := by
  have hs : fixedOuterHom m (Multiplicative.ofAdd 1)*
      fixedNegativeOuterHom m (Multiplicative.ofAdd (-1))*fixedOuterHom m (Multiplicative.ofAdd 1)=
        outerFixedReflection m := by
    rw [fixedNegativeOuterHom_value]
    have he : fixedOuterWeyl m 1=outerFixedReflection m := Subtype.ext (fixedOuterWeyl_one_val m)
    simpa only [fixedOuterWeyl,Units.val_one,inv_one] using he
  exact (map_triple_eq (fixedToOriginal m hm) _ _ _ hs).trans
    (originalOuterWeyl_projection m hm).symm

theorem original_outer_weyl_fixed (m : ℕ) (hm : 0<m) (f : MulAut (CFSG.Models.ReeF4 m))
    (hnegative : (CFSGReeFFourOriginalNegativeRootIntersections.originalNegativeRootBlock m hm false).map
      f.toMonoidHom=CFSGReeFFourOriginalNegativeRootIntersections.originalNegativeRootBlock m hm false)
    (hpositive : f (originalOuterHom m hm (Multiplicative.ofAdd 1))=
      originalOuterHom m hm (Multiplicative.ofAdd 1)) :
    f (originalOuterWeyl m hm)=originalOuterWeyl m hm := by
  have hnegative1 := negative_outer_one_fixed m hm f hnegative hpositive
  exact (congrArg f (original_outer_weyl_word m hm)).symm.trans
    ((triple_fixed f.toMonoidHom _ _ hpositive hnegative1).trans (original_outer_weyl_word m hm))

theorem original_negative_outer_conjugation (m : ℕ) (hm : 0<m) (t : Multiplicative (Field m)) :
    originalNegativeOuterHom m hm t=originalOuterWeyl m hm*originalOuterHom m hm t*
      (originalOuterWeyl m hm)⁻¹ := by
  have he := map_conjugation (fixedToOriginal m hm) (outerFixedReflection m) (fixedOuterHom m t)
  exact he.trans (congrArg (fun w : CFSG.Models.ReeF4 m=>w*originalOuterHom m hm t*w⁻¹)
    (originalOuterWeyl_projection m hm).symm)

theorem original_negative_outer_field_action (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (htau : ∀a : Field m,outerAction m hm f a=tau a)
    (t : Multiplicative (Field m)) :
    f.val (originalNegativeOuterHom m hm t)=
      originalNegativeOuterHom m hm (Multiplicative.ofAdd (tau t.toAdd)) := by
  have hX (s : Multiplicative (Field m)) : f.val (originalOuterHom m hm s)=
      originalOuterHom m hm (Multiplicative.ofAdd (tau s.toAdd)) :=
    (outerRestriction_intertwines m hm f s.toAdd).symm.trans
      (congrArg (fun a : Field m=>originalOuterHom m hm (Multiplicative.ofAdd a)) (htau s.toAdd))
  have h1 : f.val (originalOuterHom m hm (Multiplicative.ofAdd 1))=
      originalOuterHom m hm (Multiplicative.ofAdd 1) := by
    have hh := hX (Multiplicative.ofAdd 1)
    simpa only [toAdd_ofAdd,map_one] using hh
  have hW := original_outer_weyl_fixed m hm f.val
    (original_negative_root_block_map_eq m hm f.val
      (pair_preserves_positive m hm f) (pair_preserves_negative m hm f) false) h1
  calc
    f.val (originalNegativeOuterHom m hm t)=
        f.val (originalOuterWeyl m hm*originalOuterHom m hm t*(originalOuterWeyl m hm)⁻¹) :=
      congrArg f.val (original_negative_outer_conjugation m hm t)
    _=originalOuterWeyl m hm*f.val (originalOuterHom m hm t)*(originalOuterWeyl m hm)⁻¹ :=
      map_conjugate_fixed f.val.toMonoidHom _ _ hW
    _=originalOuterWeyl m hm*originalOuterHom m hm (Multiplicative.ofAdd (tau t.toAdd))*
        (originalOuterWeyl m hm)⁻¹ := conjugate_eq _ (hX t)
    _=originalNegativeOuterHom m hm (Multiplicative.ofAdd (tau t.toAdd)) :=
      (original_negative_outer_conjugation m hm _).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalSignedOuterField
