import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleField
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonPositiveActions
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWeylConstantWord

/-! The genuine middle constant word remains a literal source word
when the negative middle scalar is retained. Its projection describes
the image of W under a normalized ORIGINAL automorphism. No scalar
constraint or quotient-automorphism lift is assumed here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleWeylScalarWord
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence CFSGReeFFourPerfectProjection
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleWeylConstantWord
open CFSGReeFFourOppositeGenerationAssembly CFSGReeFFourOriginalNegativeMiddleCoordinates
open CFSGReeFFourOriginalMiddleTorusAction CFSGReeFFourOriginalNegativeMiddleRestriction
open CFSGReeFFourOriginalMiddleSemilinear CFSGReeFFourOriginalCommonPositiveActions
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPositiveNormalization

private theorem mapped_conjugated_product {G H : Type*} [Group G] [Group H]
    (F : G→*H) (w a x b : G) :
    F (a*(w*x*w⁻¹)*b)=F a*(F w*F x*(F w)⁻¹)*F b := by
  simp only [map_mul,map_inv]

private theorem map_three {G : Type*} [Group G] (F : G→*G)
    (w a y b a' y' b' : G) (hw : w=a*y*b)
    (ha : F a=a') (hy : F y=y') (hb : F b=b') : F w=a'*y'*b' := by
  rw [hw,map_mul,map_mul,ha,hy,hb]

def scaledMiddleWeylWord (m : ℕ) (c : Field m) : originalModelFixed m :=
  fixedMiddleParameter m (0,1)*
    (fixedMiddleWeyl m*fixedMiddleParameter m (c,0)*(fixedMiddleWeyl m)⁻¹)*
      fixedMiddleParameter m (1,1)

theorem scaledMiddleWeylWord_one (m : ℕ) : scaledMiddleWeylWord m 1=fixedMiddleWeyl m := by
  apply Subtype.ext
  exact (middleRelativeWeyl_constant_factors m).symm

theorem scaledMiddleWeylWord_projection (m : ℕ) (hm : 0<m) (c : Field m) :
    fixedToOriginal m hm (scaledMiddleWeylWord m c)=
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 0 1)*
        originalNegativeMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m c 0)*
          originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 1 1) := by
  have he := mapped_conjugated_product (fixedToOriginal m hm) (fixedMiddleWeyl m)
    (fixedMiddleParameter m (0,1)) (fixedMiddleParameter m (c,0)) (fixedMiddleParameter m (1,1))
  change fixedToOriginal m hm (scaledMiddleWeylWord m c)=_ at he
  rw [←originalMiddleEmbedding_coordinate,←originalMiddleEmbedding_coordinate,
    ←originalMiddleEmbedding_coordinate] at he
  exact he.trans (congrArg (fun z=>
    originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 0 1)*z*
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 1 1))
    (originalNegativeMiddleEmbedding_conjugation m hm
      (CFSGSuzukiUnipotent.coordinateElement m c 0)).symm)

theorem original_middle_weyl_word (m : ℕ) (hm : 0<m) :
    originalMiddleWeyl m hm=
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 0 1)*
        originalNegativeMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 1 0)*
          originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 1 1) := by
  have he := congrArg (fixedToOriginal m hm) (scaledMiddleWeylWord_one m).symm
  exact he.trans (scaledMiddleWeylWord_projection m hm 1)

private theorem positive_coordinate_field_action (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) (tau : Field m ≃+* Field m)
    (hfields : positiveLayerDescription m hm f tau tau) (a b : Field m) :
    f.val (originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m a b))=
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m (tau a) (tau b)) := by
  have he := middleRestriction_embedding m hm f (CFSGSuzukiUnipotent.coordinateElement m a b)
  change originalMiddleEmbedding m hm
    (middleAction m hm f (CFSGSuzukiUnipotent.coordinateElement m a b))=_ at he
  exact he.symm.trans (congrArg (originalMiddleEmbedding m hm)
    (middleAction_coordinate m hm f tau hfields a b))

theorem pair_image_middle_weyl_scaled_word (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau)
    (c : Field m)
    (hc : negativeMiddleAction m hm f (CFSGSuzukiUnipotent.coordinateElement m 1 0)=
      CFSGSuzukiUnipotent.coordinateElement m c 0) :
    f.val (originalMiddleWeyl m hm)=fixedToOriginal m hm (scaledMiddleWeylWord m c) := by
  have h01 : f.val (originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 0 1))=
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 0 1) := by
    simpa only [map_zero,map_one] using positive_coordinate_field_action m hm f tau hfields 0 1
  have h11 : f.val (originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 1 1))=
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.coordinateElement m 1 1) := by
    simpa only [map_one] using positive_coordinate_field_action m hm f tau hfields 1 1
  have h10 := negativeMiddleAction_embedding m hm f (CFSGSuzukiUnipotent.coordinateElement m 1 0)
  rw [hc] at h10
  exact (map_three f.val.toMonoidHom _ _ _ _ _ _ _ (original_middle_weyl_word m hm)
    h01 h10.symm h11).trans (scaledMiddleWeylWord_projection m hm c).symm

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleWeylScalarWord
