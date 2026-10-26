import SymmetricSubgroupAsymptotics.SubgroupActionIntersectionTransport
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Functoriality and intrinsic invariance of an actual conjugate
intersection. The automorphism acts only on its own group, not on any
ambient cyclic block used to recognize the intersection later. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.ConjugateIntersectionFunctor
variable {G H : Type*} [Group G] [Group H]

theorem map_comap_conjugate (f : G →* H) (U : Subgroup G) (g : G) :
    (U.comap (MulAut.conj g).toMonoidHom).map f=
      (U.map f).comap (MulAut.conj (f g)).toMonoidHom := by
  have he : U.comap (MulAut.conj g).toMonoidHom=
      U.map (MulAut.conj g⁻¹).toMonoidHom := by
    simpa only [inv_inv] using
      (SubgroupActionIntersectionTransport.map_eq_comap_inverse (MulAut.conj) U g⁻¹).symm
  rw [he,CFSGSubgroupConjugateRestriction.map_conjugate,map_inv,
    SubgroupActionIntersectionTransport.map_eq_comap_inverse (MulAut.conj)]
  simp only [inv_inv]

theorem invariant_intersection (f : MulAut G) (U : Subgroup G) (g : G)
    (hU : U.map f.toMonoidHom=U) (hg : f g=g) :
    (U⊓U.comap (MulAut.conj g).toMonoidHom).map f.toMonoidHom=
      U⊓U.comap (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_inf _ _ f.toMonoidHom f.injective,map_comap_conjugate,hU]
  exact congrArg (fun x : G => U⊓U.comap (MulAut.conj x).toMonoidHom) hg

end SymmetricSubgroupAsymptotics.ConjugateIntersectionFunctor
