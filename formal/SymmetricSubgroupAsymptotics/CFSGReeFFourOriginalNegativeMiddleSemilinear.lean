import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleRestriction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleSemilinear
import SymmetricSubgroupAsymptotics.CFSGReeFFourTorusScalarCoordinates

/-! The genuine original negative middle restriction normalizes the
native Suzuki torus. Every required conjugator is an actual element of
the intrinsic diagonal; no negative normalizer premise is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleSemilinear
open CFSGReeFFourOriginalNegativeMiddleRestriction CFSGReeFFourOriginalNegativeMiddleCoordinates
open CFSGReeFFourOriginalPairRestriction CFSGReeFFourOriginalPairDiagonal
open CFSGReeFFourOriginalMiddleTorusAction CFSGReeFFourOriginalMiddleSemilinear
open CFSGReeFFourFieldParameters CFSGReeFFourFixedTorus CFSGReeFFourPerfectProjection
open CFSGReeFFourFixedDiagonalCardinality CFSGReeFFourFixedMiddleTorusAction
open CFSGReeFFourTorusScalarCoordinates CFSGCoordinateConjugationNormalizer

private theorem transported_action {C G : Type*} [Group G] (i j : C→G) (w d : G)
    (R : C→C) (hj : ∀x,j x=w*i x*w⁻¹) (hR : ∀x,i (R x)=d*i x*d⁻¹) (x : C) :
    j (R x)=(w*d*w⁻¹)*j x*(w*d*w⁻¹)⁻¹ := by
  calc
    j (R x)=w*i (R x)*w⁻¹ := hj _
    _=w*(d*i x*d⁻¹)*w⁻¹ := congrArg (fun z=>w*z*w⁻¹) (hR x)
    _=(w*d*w⁻¹)*j x*(w*d*w⁻¹)⁻¹ := by rw [hj];group

private theorem inverse_conj_mem {G : Type*} [Group G] (D : Subgroup G) (w x : G)
    (hw : w∈Subgroup.normalizer (D : Set G)) (hx : x∈D) : w⁻¹*x*w∈D := by
  have hwi := (Subgroup.normalizer (D : Set G)).inv_mem hw
  simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hwi x).mp hx

private theorem invert_conjugation {G : Type*} [Group G] (w x t : G)
    (he : w⁻¹*x*w=t) : x=w*t*w⁻¹ := by rw [←he];group

private theorem conjugator_eq {G : Type*} [Group G] {a b : G} (he : a=b) (x : G) :
    a*x*a⁻¹=b*x*b⁻¹ := congrArg (fun z=>z*x*z⁻¹) he

private theorem middleScalar_outer (m : ℕ) (c : (Field m)ˣ) : middleScalar m c 1=c⁻¹ := by
  rw [middle_scalar_formula]
  simp only [one_pow,map_one,inv_one,mul_one]

theorem negativeMiddleAction_conjugate_torus (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) (c : (Field m)ˣ) :
    ∃r : (Field m)ˣ,negativeMiddleAction m hm f*CFSGSuzukiUnipotent.torusAutHom m c*
      (negativeMiddleAction m hm f)⁻¹=CFSGSuzukiUnipotent.torusAutHom m r := by
  let W : CFSG.Models.ReeF4 m := originalMiddleWeyl m hm
  let dp : CFSG.Models.ReeF4 m := fixedToOriginal m hm (fixedTorus m c 1)
  let dn : CFSG.Models.ReeF4 m := W*dp*W⁻¹
  have hd : dp∈originalDiagonal m hm := by
    rw [←fixedDiagonal_map_originalDiagonal]
    exact ⟨fixedTorus m c 1,fixedTorus_mem_diagonal m c 1,rfl⟩
  have hw : W∈Subgroup.normalizer (originalDiagonal m hm : Set (CFSG.Models.ReeF4 m)) :=
    originalMiddleWeyl_normalizes_diagonal m hm
  have hdn : dn∈originalDiagonal m hm := (Subgroup.mem_normalizer_iff.mp hw dp).mp hd
  have hfd : f.val dn∈originalDiagonal m hm := by
    rw [←originalDiagonal_map_pair m hm f]
    exact ⟨dn,hdn,rfl⟩
  have hy := inverse_conj_mem (originalDiagonal m hm) W (f.val dn) hw hfd
  obtain ⟨u,v,huv⟩ := exists_originalDiagonal_torus m hm _ hy
  have hconj : f.val dn=W*fixedToOriginal m hm (fixedTorus m u v)*W⁻¹ :=
    invert_conjugation W (f.val dn) _ huv
  let r := (middleScalar m u v)⁻¹
  have hRp (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.torusAutHom m c x)=
        dp*originalMiddleEmbedding m hm x*dp⁻¹ := by
    simpa only [middleScalar_outer,inv_inv] using original_fixed_torus_middle_action m hm c 1 x
  have hR (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      originalNegativeMiddleEmbedding m hm (CFSGSuzukiUnipotent.torusAutHom m c x)=
        dn*originalNegativeMiddleEmbedding m hm x*dn⁻¹ :=
    transported_action (originalMiddleEmbedding m hm) (originalNegativeMiddleEmbedding m hm) W dp
      (CFSGSuzukiUnipotent.torusAutHom m c) (originalNegativeMiddleEmbedding_conjugation m hm) hRp x
  have hR' (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      originalNegativeMiddleEmbedding m hm (CFSGSuzukiUnipotent.torusAutHom m r x)=
        f.val dn*originalNegativeMiddleEmbedding m hm x*(f.val dn)⁻¹ := by
    have he := transported_action (originalMiddleEmbedding m hm) (originalNegativeMiddleEmbedding m hm)
      W (fixedToOriginal m hm (fixedTorus m u v)) (CFSGSuzukiUnipotent.torusAutHom m r)
      (originalNegativeMiddleEmbedding_conjugation m hm) (original_fixed_torus_middle_action m hm u v) x
    exact he.trans (conjugator_eq hconj.symm _)
  refine ⟨r,?_⟩
  apply MulEquiv.ext
  intro x
  exact coordinate_conjugate_apply (originalNegativeMiddleEmbedding m hm)
    (originalNegativeMiddleEmbedding_injective m hm) f.val (negativeMiddleAction m hm f).toEquiv
    (CFSGSuzukiUnipotent.torusAutHom m c) (CFSGSuzukiUnipotent.torusAutHom m r) dn
    (negativeMiddleAction_embedding m hm f) hR hR' x

theorem negativeMiddleAction_mem_torus_normalizer (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) :
    negativeMiddleAction m hm f∈Subgroup.normalizer
      ((CFSGSuzukiUnipotent.torusAutHom m).range :
        Set (MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m))) := by
  have hc (g : pairStabilizer m hm) (R : MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m))
      (hR : R∈(CFSGSuzukiUnipotent.torusAutHom m).range) :
      negativeMiddleAction m hm g*R*(negativeMiddleAction m hm g)⁻¹∈
        (CFSGSuzukiUnipotent.torusAutHom m).range := by
    obtain ⟨c,rfl⟩ := hR
    obtain ⟨r,hr⟩ := negativeMiddleAction_conjugate_torus m hm g c
    exact ⟨r,hr.symm⟩
  exact hom_mem_normalizer_of_conjugate_closed (negativeMiddleRestriction m hm)
    (CFSGSuzukiUnipotent.torusAutHom m).range hc f

theorem negativeMiddleAction_firstLayer_scalar_ringAut (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    ∃!p : (Field m)ˣ×(Field m ≃+* Field m),
      ∀x : CFSGSuzukiUnipotent.unipotentSubgroup m,
        CFSGSuzukiUnipotent.firstParameter m (negativeMiddleAction m hm f x)=
          (p.1 : Field m)*p.2 (CFSGSuzukiUnipotent.firstParameter m x) :=
  CFSGSuzukiUnipotent.firstLayer_scalar_ringAut m hm (negativeMiddleAction m hm f)
    (negativeMiddleAction_mem_torus_normalizer m hm f)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeMiddleSemilinear
