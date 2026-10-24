import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterWeylCoset
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterTorusReflection
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedTorusGroup

/-! Genuine original torus reflection and its covariance under a
pair-preserving automorphism. The diagonal residual in the outer Weyl
coset cancels by the proved commutativity of the actual diagonal image. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterTorusCovariance
open CFSGReeFFourOriginalOuterWeylCoset CFSGReeFFourOriginalDiagonalNormalizer
open CFSGReeFFourOriginalPairDiagonal CFSGReeFFourOriginalPairRestriction
open CFSGReeFFourFieldParameters CFSGReeFFourPerfectProjection CFSGReeFFourFixedTorus
open CFSGReeFFourFixedTorusGroup CFSGReeFFourOuterTorusReflection
open CFSGReeFFourMinimalParabolics CFSGReeFFourFixedBruhatCover
open CFSGReeFFourFixedDiagonalCardinality

private theorem conj_diagonal_multiple {G : Type*} [Group G] (d w x : G)
    (h : Commute d (w*x*w⁻¹)) : (d*w)*x*(d*w)⁻¹=w*x*w⁻¹ := by
  calc
    (d*w)*x*(d*w)⁻¹=d*(w*x*w⁻¹)*d⁻¹ := by group
    _=(w*x*w⁻¹)*d*d⁻¹ := by rw [h.eq]
    _=w*x*w⁻¹ := by group

private theorem map_reflection_of_coset {G : Type*} [Group G] (F : G→*G)
    (w t t' d : G) (he : w*t*w⁻¹=t') (hw : F w=d*w)
    (hc : Commute d (w*F t*w⁻¹)) : F t'=w*F t*w⁻¹ := by
  calc
    F t'=F (w*t*w⁻¹) := congrArg F he.symm
    _=F w*F t*(F w)⁻¹ := by rw [map_mul,map_mul,map_inv]
    _=(d*w)*F t*(d*w)⁻¹ := congrArg (fun z=>z*F t*z⁻¹) hw
    _=w*F t*w⁻¹ := conj_diagonal_multiple d w (F t) hc

theorem originalDiagonal_commute (m : ℕ) (hm : 0<m)
    (x y : originalDiagonal m hm) : Commute x.val y.val := by
  obtain ⟨a,b,he⟩ := exists_originalDiagonal_torus m hm x.val x.property
  obtain ⟨c,d,hf⟩ := exists_originalDiagonal_torus m hm y.val y.property
  rw [he,hf]
  exact (Commute.all (a,b) (c,d)).map ((fixedToOriginal m hm).comp (fixedTorusHom m))

theorem original_outer_torus_reflection (m : ℕ) (hm : 0<m) (a b : (Field m)ˣ) :
    originalOuterWeyl m hm*fixedToOriginal m hm (fixedTorus m a b)*(originalOuterWeyl m hm)⁻¹=
      fixedToOriginal m hm (fixedTorus m (b*a⁻¹) b) := by
  have hw : fixedPairedWord m [false]=outerFixedReflection m :=
    (simpleWeyl_false m).trans rfl
  have he := congrArg (fixedToOriginal m hm) (fixed_outer_torus_reflection m a b)
  simpa only [map_mul,map_inv,←hw] using he

theorem pair_outer_torus_covariance (m : ℕ) (hm : 0<m) (f : pairStabilizer m hm)
    (a b : (Field m)ˣ) :
    f.val (fixedToOriginal m hm (fixedTorus m (b*a⁻¹) b))=
      originalOuterWeyl m hm*f.val (fixedToOriginal m hm (fixedTorus m a b))*
        (originalOuterWeyl m hm)⁻¹ := by
  let t := fixedToOriginal m hm (fixedTorus m a b)
  have ht : t∈originalDiagonal m hm := by
    rw [←fixedDiagonal_map_originalDiagonal]
    exact ⟨fixedTorus m a b,fixedTorus_mem_diagonal m a b,rfl⟩
  have hft : f.val t∈originalDiagonal m hm := by
    rw [←originalDiagonal_map_pair m hm f]
    exact ⟨t,ht,rfl⟩
  have hN := originalPairedWord_normalizes_diagonal m hm [false]
  have hconj : originalOuterWeyl m hm*f.val t*(originalOuterWeyl m hm)⁻¹∈originalDiagonal m hm :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp hft
  obtain ⟨d,hd⟩ := pair_image_outerWeyl_mem_diagonal_coset m hm f
  have hc := originalDiagonal_commute m hm d ⟨_,hconj⟩
  exact map_reflection_of_coset f.val.toMonoidHom (originalOuterWeyl m hm) t
    (fixedToOriginal m hm (fixedTorus m (b*a⁻¹) b)) d.val
    (original_outer_torus_reflection m hm a b) hd hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalOuterTorusCovariance
