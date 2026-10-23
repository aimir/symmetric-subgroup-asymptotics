import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateRestriction

/-! Conjugation commutes with the literal preimage of any group map.
No injectivity, quotient recognition, or fixed-lift hypothesis is needed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGConjugateComap
variable {G H : Type*} [Group G] [Group H]

theorem comap_conjugate (f : G →* H) (R : Subgroup H) (g : G) :
    (R.map (MulAut.conj (f g)).toMonoidHom).comap f =
      (R.comap f).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_equiv_eq_comap_symm',Subgroup.map_equiv_eq_comap_symm',
    Subgroup.comap_comap,Subgroup.comap_comap]
  congr 1
  ext x
  change (f g)⁻¹ * f x * f g = f (g⁻¹*x*g)
  simp only [map_mul,map_inv]

theorem conjugate_comap_eq_of_conjugate_eq (f : G →* H) (R : Subgroup H)
    (g h : G)
    (he : R.map (MulAut.conj (f g)).toMonoidHom =
      R.map (MulAut.conj (f h)).toMonoidHom) :
    (R.comap f).map (MulAut.conj g).toMonoidHom =
      (R.comap f).map (MulAut.conj h).toMonoidHom := by
  have hh := congrArg (fun S : Subgroup H => S.comap f) he
  simpa only [comap_conjugate] using hh

end SymmetricSubgroupAsymptotics.CFSGConjugateComap
