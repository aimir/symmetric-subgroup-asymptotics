import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairRestriction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalNormalizer

/-! The actual intrinsic negative middle block carries a genuine native
Suzuki-U action of the original pair stabilizer. Every restriction and
coordinate intertwiner is proved on the original quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleRestriction
open CFSGReeFFourOriginalNegativeMiddleCoordinates CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourOriginalNegativeRootIntersections CFSGReeFFourOriginalSignedRootAction
open CFSGReeFFourOriginalDiagonalNormalizer CFSGReeFFourOriginalPairDiagonal
open CFSGReeFFourPerfectProjection CFSGReeFFourMinimalParabolics
open CFSGInvariantSubgroupCoordinateImage

def negativeBlockRestriction (m : ℕ) (hm : 0<m) :
    pairStabilizer m hm →* MulAut (originalNegativeRootBlock m hm true) where
  toFun f := restrictAut (originalNegativeRootBlock m hm true) f.val
    (original_negative_root_block_map_eq m hm f.val
      (pair_preserves_positive m hm f) (pair_preserves_negative m hm f) true)
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

def negativeMiddleRestriction (m : ℕ) (hm : 0<m) :
    pairStabilizer m hm →* MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m) :=
  (MulAut.congr (originalNegativeMiddleEquiv m hm).symm).toMonoidHom.comp
    (negativeBlockRestriction m hm)

def negativeMiddleAction (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) :
    MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m) := negativeMiddleRestriction m hm f

private theorem inverse_congr_intertwines {C H : Type*} [Group C] [Group H]
    (e : C≃*H) (R : MulAut H) (x : C) : e ((MulAut.congr e.symm) R x)=R (e x) := by
  change e (e.symm (R (e x)))=R (e x)
  exact e.apply_symm_apply _

theorem negativeMiddleAction_embedding (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
    originalNegativeMiddleEmbedding m hm (negativeMiddleAction m hm f x)=
      f.val (originalNegativeMiddleEmbedding m hm x) := by
  have he := inverse_congr_intertwines (originalNegativeMiddleEquiv m hm)
    (negativeBlockRestriction m hm f) x
  exact congrArg (fun z : originalNegativeRootBlock m hm true=>z.val) he

theorem originalMiddleWeyl_normalizes_diagonal (m : ℕ) (hm : 0<m) :
    originalMiddleWeyl m hm∈Subgroup.normalizer
      (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m)) := by
  have hw := originalPairedWord_normalizes_diagonal m hm [true]
  have he : originalPairedWord m hm [true]=originalMiddleWeyl m hm :=
    congrArg (fixedToOriginal m hm) (simpleWeyl_true m)
  exact he ▸hw

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleRestriction
