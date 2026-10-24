import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleCoordinates
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleTorusInversion
import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentScaledFieldActions

/-! The actual one-parameter middle torus has the inverse character on
the intrinsic negative block. Only its checked original Weyl inversion
and the genuine positive/negative coordinate embeddings are used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleTorusAction
open CFSGReeFFourOriginalNegativeMiddleCoordinates CFSGReeFFourMiddleTorusInversion
open CFSGReeFFourOriginalMiddleTorusAction CFSGReeFFourFixedMiddleTorusAction
open CFSGReeFFourFieldParameters CFSGReeFFourPerfectProjection CFSGReeFFourFixedTorus

private theorem map_inversion {G H : Type*} [Group G] [Group H] (F : G→*H) (w d : G)
    (he : w*d*w⁻¹=d⁻¹) : F w*F d*(F w)⁻¹=(F d)⁻¹ := by
  calc
    F w*F d*(F w)⁻¹=F (w*d*w⁻¹) := by rw [map_mul,map_mul,map_inv]
    _=F (d⁻¹) := congrArg F he
    _=(F d)⁻¹ := map_inv F d

private theorem conjugate_inverse_of_inversion {G : Type*} [Group G] (w d : G)
    (he : w*d*w⁻¹=d⁻¹) : w*d⁻¹*w⁻¹=d := by
  calc
    w*d⁻¹*w⁻¹=(w*d*w⁻¹)⁻¹ := by group
    _=(d⁻¹)⁻¹ := congrArg Inv.inv he
    _=d := inv_inv d

private theorem inverse_coordinate_action {C G : Type*} [Group G] (i : C→G) (d : G)
    (R S : C→C) (hRS : ∀x,R (S x)=x) (hR : ∀x,i (R x)=d*i x*d⁻¹) (x : C) :
    i (S x)=d⁻¹*i x*d := by
  have he := hR (S x)
  rw [hRS] at he
  calc
    i (S x)=d⁻¹*(d*i (S x)*d⁻¹)*d := by group
    _=d⁻¹*i x*d := congrArg (fun z=>d⁻¹*z*d) he.symm

private theorem transported_action {C G : Type*} [Group G] (i j : C→G) (w d : G)
    (R : C→C) (hj : ∀x,j x=w*i x*w⁻¹) (hR : ∀x,i (R x)=d*i x*d⁻¹) (x : C) :
    j (R x)=(w*d*w⁻¹)*j x*(w*d*w⁻¹)⁻¹ := by
  calc
    j (R x)=w*i (R x)*w⁻¹ := hj _
    _=w*(d*i x*d⁻¹)*w⁻¹ := congrArg (fun z=>w*z*w⁻¹) (hR x)
    _=(w*d*w⁻¹)*j x*(w*d*w⁻¹)⁻¹ := by rw [hj];group

private theorem conjugator_eq {G : Type*} [Group G] {a b : G} (he : a=b) (x : G) :
    a*x*a⁻¹=b*x*b⁻¹ := congrArg (fun z=>z*x*z⁻¹) he

theorem original_middle_torus_inversion (m : ℕ) (hm : 0<m) (b : (Field m)ˣ) :
    originalMiddleWeyl m hm*fixedToOriginal m hm (fixedTorus m 1 b)*(originalMiddleWeyl m hm)⁻¹=
      (fixedToOriginal m hm (fixedTorus m 1 b))⁻¹ :=
  map_inversion (fixedToOriginal m hm) _ _ (middle_fixed_torus_inversion m b)

theorem original_negative_middle_torus_action (m : ℕ) (hm : 0<m) (b : (Field m)ˣ)
    (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
    originalNegativeMiddleEmbedding m hm (CFSGSuzukiUnipotent.torusAutHom m (middleScalar m 1 b) x)=
      fixedToOriginal m hm (fixedTorus m 1 b)*originalNegativeMiddleEmbedding m hm x*
        (fixedToOriginal m hm (fixedTorus m 1 b))⁻¹ := by
  let d : CFSG.Models.ReeF4 m := fixedToOriginal m hm (fixedTorus m 1 b)
  let s := middleScalar m 1 b
  have hcancel (y : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      CFSGSuzukiUnipotent.torusAutHom m s⁻¹ (CFSGSuzukiUnipotent.torusAutHom m s y)=y := by
    rw [map_inv]
    exact (CFSGSuzukiUnipotent.torusAutHom m s).symm_apply_apply y
  have hR (y : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.torusAutHom m s y)=
        d⁻¹*originalMiddleEmbedding m hm y*(d⁻¹)⁻¹ := by
    simpa only [inv_inv] using inverse_coordinate_action (originalMiddleEmbedding m hm) d
      (CFSGSuzukiUnipotent.torusAutHom m s⁻¹) (CFSGSuzukiUnipotent.torusAutHom m s)
      hcancel (original_fixed_torus_middle_action m hm 1 b) y
  have he := transported_action (originalMiddleEmbedding m hm) (originalNegativeMiddleEmbedding m hm)
    (originalMiddleWeyl m hm) d⁻¹ (CFSGSuzukiUnipotent.torusAutHom m s)
    (originalNegativeMiddleEmbedding_conjugation m hm) hR x
  have hd : originalMiddleWeyl m hm*d⁻¹*(originalMiddleWeyl m hm)⁻¹=d :=
    conjugate_inverse_of_inversion (originalMiddleWeyl m hm) d (original_middle_torus_inversion m hm b)
  exact he.trans (conjugator_eq hd _)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleTorusAction
