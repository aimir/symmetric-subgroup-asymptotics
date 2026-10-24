import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleTorusAction
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPairDiagonal
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusScalars
import SymmetricSubgroupAsymptotics.CFSGCoordinateConjugationNormalizer

/-! The actual original middle restriction normalizes the literal
Suzuki torus. Thus its intrinsic first layer is scalar-semilinear over
the same field. No whole rank-one recognition or Aut lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleSemilinear
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourOriginalPairDiagonal CFSGReeFFourOriginalMiddleTorusAction
open CFSGReeFFourFixedMiddleTorusAction CFSGReeFFourOriginalRootCoordinates
open CFSGReeFFourOriginalRootIntersections CFSGReeFFourPerfectProjection
open CFSGReeFFourFixedTorus CFSGReeFFourFixedTorusScalars
open CFSGReeFFourFixedDiagonalCardinality CFSGCoordinateConjugationNormalizer
open CFSGIntegerMatrixPowerHom CFSGFFourRelativeScalarIndex

private theorem inverse_intertwines {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (r : MulAut G) (R : MulAut H)
    (h : ∀ x,R (e x)=e (r x)) (y : H) : e.symm (R y)=r (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply,←h,e.apply_symm_apply]

theorem middleRestriction_embedding (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
    originalMiddleEmbedding m hm (middleRestriction m hm f x)=
      f.val (originalMiddleEmbedding m hm x) := by
  have he := inverse_intertwines (originalMiddleSuzukiEquiv m hm)
    (rootBlockRestriction m hm true f) (middleRestriction m hm f)
    (middleRestriction_intertwines m hm f) x
  have hv := congrArg (fun z : originalRootBlock m hm true=>z.val) he
  simpa only [rootBlockRestriction_val] using hv

private theorem middleScalar_outer (m : ℕ) (a : (Field m)ˣ) : middleScalar m a 1=a⁻¹ := by
  change powerHom relativeCartan (fixedTorusTuple m a 1) 1=a⁻¹
  rw [fixed_torus_scalars]
  rfl

/-- A typed value of the concrete restriction hom for coordinate group algebra. -/
def middleAction (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm) :
    MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m) := middleRestriction m hm f

theorem middleAction_apply (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
    middleAction m hm f x=middleRestriction m hm f x := rfl

theorem middleRestriction_conjugate_torus (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) (c : (Field m)ˣ) :
    ∃ r : (Field m)ˣ,middleAction m hm f*CFSGSuzukiUnipotent.torusAutHom m c*
      (middleAction m hm f)⁻¹=CFSGSuzukiUnipotent.torusAutHom m r := by
  let d := fixedToOriginal m hm (fixedTorus m c 1)
  have hd : d∈originalDiagonal m hm := by
    rw [←fixedDiagonal_map_originalDiagonal m hm]
    exact ⟨fixedTorus m c 1,fixedTorus_mem_diagonal m c 1,rfl⟩
  have hfd : f.val d∈originalDiagonal m hm := by
    rw [←originalDiagonal_map_pair m hm f]
    exact ⟨d,hd,rfl⟩
  obtain ⟨u,v,huv⟩ := exists_originalDiagonal_torus m hm (f.val d) hfd
  let r := (middleScalar m u v)⁻¹
  refine ⟨r,?_⟩
  have hR (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.torusAutHom m c x)=
        d*originalMiddleEmbedding m hm x*d⁻¹ := by
    have he := original_fixed_torus_middle_action m hm c 1 x
    rw [middleScalar_outer,inv_inv] at he
    exact he
  have hR' (x : CFSGSuzukiUnipotent.unipotentSubgroup m) :
      originalMiddleEmbedding m hm (CFSGSuzukiUnipotent.torusAutHom m r x)=
        f.val d*originalMiddleEmbedding m hm x*(f.val d)⁻¹ := by
    rw [huv]
    exact original_fixed_torus_middle_action m hm u v x
  apply MulEquiv.ext
  intro x
  exact coordinate_conjugate_apply (originalMiddleEmbedding m hm)
    (originalMiddleEmbedding_injective m hm) f.val (middleAction m hm f).toEquiv
    (CFSGSuzukiUnipotent.torusAutHom m c) (CFSGSuzukiUnipotent.torusAutHom m r) d
    (middleRestriction_embedding m hm f) hR hR' x

theorem middleRestriction_mem_torus_normalizer (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    middleAction m hm f∈Subgroup.normalizer ((CFSGSuzukiUnipotent.torusAutHom m).range :
      Set (MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m))) := by
  have hc (g : pairStabilizer m hm) (R : MulAut (CFSGSuzukiUnipotent.unipotentSubgroup m))
      (hR : R∈(CFSGSuzukiUnipotent.torusAutHom m).range) :
      middleAction m hm g*R*(middleAction m hm g)⁻¹∈(CFSGSuzukiUnipotent.torusAutHom m).range := by
    obtain ⟨c,rfl⟩ := hR
    obtain ⟨r,hr⟩ := middleRestriction_conjugate_torus m hm g c
    exact ⟨r,hr.symm⟩
  exact hom_mem_normalizer_of_conjugate_closed (middleRestriction m hm)
    (CFSGSuzukiUnipotent.torusAutHom m).range hc f


theorem middleRestriction_firstLayer_scalar_ringAut (m : ℕ) (hm : 0<m)
    (f : pairStabilizer m hm) :
    ∃! p : (Field m)ˣ×(Field m ≃+* Field m),
      ∀ x : CFSGSuzukiUnipotent.unipotentSubgroup m,
        CFSGSuzukiUnipotent.firstParameter m (middleAction m hm f x)=
          (p.1 : Field m)*p.2 (CFSGSuzukiUnipotent.firstParameter m x) :=
  CFSGSuzukiUnipotent.firstLayer_scalar_ringAut m hm (middleAction m hm f)
    (middleRestriction_mem_torus_normalizer m hm f)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalMiddleSemilinear
