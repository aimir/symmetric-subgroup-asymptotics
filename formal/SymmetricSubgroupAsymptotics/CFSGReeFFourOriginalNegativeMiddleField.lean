import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleSemilinear
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalCommonDiagonalAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleScalarSurjectivity
import SymmetricSubgroupAsymptotics.CFSGScalarSemilinearConjugationCharacters

/-! The genuine negative middle restriction has the SAME field map as
the normalized positive blocks. Its nonzero scalar is retained until a
separate actual middle-Weyl constraint proves it is one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleField
open CFSGReeFFourOriginalNegativeMiddleSemilinear CFSGReeFFourOriginalNegativeMiddleTorusAction
open CFSGReeFFourOriginalNegativeMiddleRestriction CFSGReeFFourOriginalNegativeMiddleCoordinates
open CFSGReeFFourOriginalCommonDiagonalAction CFSGReeFFourMiddleScalarSurjectivity
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPositiveNormalization
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus CFSGReeFFourPerfectProjection
open CFSGReeFFourFixedMiddleTorusAction CFSGReeFFourTorusScalarCoordinates
open CFSGScalarSemilinearConjugationCharacters SemilinearScalarPairRigidity

private theorem conjugator_eq {G : Type*} [Group G] {a b : G} (he : a=b) (x : G) :
    a*x*a⁻¹=b*x*b⁻¹ := congrArg (fun z=>z*x*z⁻¹) he

private theorem middleScalar_field_map (m : ℕ) (tau : Field m ≃+* Field m) (b : (Field m)ˣ) :
    middleScalar m 1 (Units.map tau.toMonoidHom b)=Units.map tau.toMonoidHom (middleScalar m 1 b) := by
  have he := congrArg Prod.snd (scalarPair_field_map m tau 1 b)
  simpa only [map_one] using he

theorem negative_middle_field_eq (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau)
    (c : (Field m)ˣ) (sigma : Field m ≃+* Field m)
    (hfirst : ∀x : CFSGSuzukiUnipotent.unipotentSubgroup m,
      CFSGSuzukiUnipotent.firstParameter m (negativeMiddleAction m hm f x)=
        (c : Field m)*sigma (CFSGSuzukiUnipotent.firstParameter m x)) : sigma=tau := by
  apply ringEquiv_eq_of_units
  intro u
  obtain ⟨b,hb⟩ := middleScalar_surjective m u⁻¹
  have hF : f.val (fixedToOriginal m hm (fixedTorus m 1 b))=
      fixedToOriginal m hm (fixedTorus m 1 (Units.map tau.toMonoidHom b)) := by
    simpa only [map_one] using original_torus_field_action m hm f tau hfields 1 b
  have hR' (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      originalNegativeMiddleEmbedding m hm
        (CFSGSuzukiUnipotent.torusAutHom m (middleScalar m 1 (Units.map tau.toMonoidHom b)) x)=
      f.val (fixedToOriginal m hm (fixedTorus m 1 b))*originalNegativeMiddleEmbedding m hm x*
        (f.val (fixedToOriginal m hm (fixedTorus m 1 b)))⁻¹ :=
    (original_negative_middle_torus_action m hm (Units.map tau.toMonoidHom b) x).trans
      (conjugator_eq hF.symm _)
  have he := character_eq_of_scalar_semilinear_conjugation (originalNegativeMiddleEmbedding m hm)
    (originalNegativeMiddleEmbedding_injective m hm) f.val (negativeMiddleAction m hm f)
    (CFSGSuzukiUnipotent.torusAutHom m (middleScalar m 1 b))
    (CFSGSuzukiUnipotent.torusAutHom m (middleScalar m 1 (Units.map tau.toMonoidHom b)))
    (fixedToOriginal m hm (fixedTorus m 1 b)) (CFSGSuzukiUnipotent.firstParameter m) sigma.toRingHom
    ((middleScalar m 1 b : Field m)⁻¹) ((middleScalar m 1 (Units.map tau.toMonoidHom b) : Field m)⁻¹)
    (c : Field m) c.ne_zero (negativeMiddleAction_embedding m hm f)
    (original_negative_middle_torus_action m hm b) hR' hfirst
    (CFSGSuzukiUnipotentScaledFieldActions.first_torus m _)
    (CFSGSuzukiUnipotentScaledFieldActions.first_torus m _)
    (CFSGSuzukiUnipotent.coordinateElement m 1 0) rfl
  have htarget : (middleScalar m 1 (Units.map tau.toMonoidHom b) : Field m)⁻¹=
      tau ((middleScalar m 1 b : Field m)⁻¹) := by
    rw [middleScalar_field_map]
    change (tau (middleScalar m 1 b : Field m))⁻¹=tau ((middleScalar m 1 b : Field m)⁻¹)
    exact (map_inv₀ tau _).symm
  have hsame := he.symm.trans htarget
  apply Units.ext
  simpa only [hb,Units.val_inv_eq_inv_val,inv_inv] using hsame

theorem exists_negative_middle_scaled_common_field (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (tau : Field m ≃+* Field m) (hfields : positiveLayerDescription m hm f tau tau) :
    ∃c : (Field m)ˣ,
      negativeMiddleAction m hm f=CFSGSuzukiUnipotent.torusAutHom m c⁻¹*
        CFSGSuzukiUnipotentFieldActions.fieldAut m tau ∧
      negativeMiddleAction m hm f (CFSGSuzukiUnipotent.coordinateElement m 1 0)=
        CFSGSuzukiUnipotent.coordinateElement m (c : Field m) 0 := by
  obtain ⟨⟨c,sigma⟩,hfirst,_⟩ := negativeMiddleAction_firstLayer_scalar_ringAut m hm f
  have he := negative_middle_field_eq m hm f tau hfields c sigma hfirst
  subst sigma
  refine ⟨c,CFSGSuzukiUnipotentScaledFieldActions.eq_scaled_fieldAut_of_first m hm
    (negativeMiddleAction m hm f) (negativeMiddleAction_mem_torus_normalizer m hm f) c tau hfirst,?_⟩
  simpa only [map_one,map_zero,mul_one,mul_zero] using
    CFSGSuzukiUnipotentScaledFieldActions.coordinate_action_of_scaled_first m hm
      (negativeMiddleAction m hm f) (negativeMiddleAction_mem_torus_normalizer m hm f) c tau hfirst 1 0

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleField
