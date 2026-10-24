import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalTorusRestriction
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalarSurjectivity

/-! Actual inner torus normalization removes both positive scalar
coefficients. The two remaining field maps are kept separate until a
genuine original-group coupling relation proves they agree. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalization
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourOriginalOuterSemilinear CFSGReeFFourOriginalMiddleSemilinear
open CFSGReeFFourOriginalTorusRestriction CFSGReeFFourFixedTorusScalarSurjectivity
open CFSGReeFFourPerfectProjection CFSGReeFFourFixedTorus
open CFSGReeFFourFixedMiddleTorusAction CFSGReeFFourFixedOuterTorusAction
open CFSGFiniteFieldScalarNormalizer

private theorem middleTorus_first (m : ℕ) (hm : 0<m) (s : (Field m)ˣ)
    (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
    CFSGSuzukiUnipotent.firstParameter m (CFSGSuzukiUnipotent.torusAutHom m s⁻¹ x)=
      (s : Field m)*CFSGSuzukiUnipotent.firstParameter m x := by
  have he := CFSGSuzukiUnipotent.firstLayerAddAut_first m hm
    (CFSGSuzukiUnipotent.torusAutHom m s⁻¹) x
  change CFSGSuzukiUnipotent.firstLayerAutHom m hm
    (CFSGSuzukiUnipotent.torusAutHom m s⁻¹) (CFSGSuzukiUnipotent.firstParameter m x)=_ at he
  rw [CFSGSuzukiUnipotent.firstLayer_torusAut,inv_inv] at he
  exact he.symm

/-- The two positive field descriptions, with a fixed typed source automorphism. -/
def positiveLayerDescription (m : ℕ) (hm : 0<m) (g : pairStabilizer m hm)
    (tau nu : Field m ≃+* Field m) : Prop :=
  (∀ x : Field m,outerAction m hm g x=tau x) ∧
    (∀ x : CFSGSuzukiUnipotent.unipotentSubgroup m,
      CFSGSuzukiUnipotent.firstParameter m (middleAction m hm g x)=
        nu (CFSGSuzukiUnipotent.firstParameter m x))

/-- Pointwise inner adjustment, keeping automorphism multiplication out of concrete types. -/
def innerAdjusted (m : ℕ) (hm : 0<m) (f g : pairStabilizer m hm)
    (z : CFSG.Models.ReeF4 m) : Prop :=
  ∀ x : CFSG.Models.ReeF4 m,g.val x=z*f.val x*z⁻¹

theorem exists_inner_normalized_positive_layers (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    ∃ (z : CFSG.Models.ReeF4 m) (g : pairStabilizer m hm)
      (tau nu : Field m ≃+* Field m),
      innerAdjusted m hm f g z ∧ positiveLayerDescription m hm g tau nu := by
  obtain ⟨⟨co,tau⟩,ho,_⟩ := outerRestriction_scalar_ringAut m hm f
  obtain ⟨⟨cm,nu⟩,hmid,_⟩ := middleRestriction_firstLayer_scalar_ringAut m hm f
  obtain ⟨⟨a,b⟩,hab⟩ := scalar_pair_surjective m (co⁻¹,cm⁻¹)
  have houter : outerScalar m a b=co⁻¹ := congrArg Prod.fst hab
  have hmiddle : middleScalar m a b=cm⁻¹ := congrArg Prod.snd hab
  let g : pairStabilizer m hm := torusPairAut m hm a b*f
  refine ⟨fixedToOriginal m hm (fixedTorus m a b),g,tau,nu,?_,?_,?_⟩
  · intro x
    rfl
  · intro x
    have he := congrArg (fun A : AddAut (Field m)=>A x)
      (map_mul (outerRestriction m hm) (torusPairAut m hm a b) f)
    change outerAction m hm g x=
      outerAction m hm (torusPairAut m hm a b) (outerAction m hm f x) at he
    rw [outerAction_torusPairAut] at he
    change outerAction m hm g x=(outerScalar m a b : Field m)*outerAction m hm f x at he
    rw [houter,ho,Units.val_inv_eq_inv_val,inv_mul_cancel_left₀ co.ne_zero] at he
    exact he
  · intro x
    have he := congrArg (fun A : MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m)=>
      CFSGSuzukiUnipotent.firstParameter m (A x))
      (map_mul (middleRestriction m hm) (torusPairAut m hm a b) f)
    change CFSGSuzukiUnipotent.firstParameter m (middleAction m hm g x)=
      CFSGSuzukiUnipotent.firstParameter m
        (middleAction m hm (torusPairAut m hm a b) (middleAction m hm f x)) at he
    rw [middleAction_torusPairAut,middleTorus_first m hm,hmiddle,hmid,
      Units.val_inv_eq_inv_val,inv_mul_cancel_left₀ cm.ne_zero] at he
    exact he

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalization
