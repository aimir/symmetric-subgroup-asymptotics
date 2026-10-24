import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Ring.Hom.Defs

/-! A scalar character of a conjugation action is transported by the
field map on any nonzero first-layer coordinate. This does not require
that the whole coordinate object be a one-dimensional root group. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGSemilinearConjugationCharacters

theorem character_eq_of_semilinear_conjugation {G C K : Type*} [Group G] [Semiring K]
    (i : C→G) (hi : Function.Injective i) (F : MulAut G) (A R R' : C→C)
    (d : G) (p : C→K) (sigma : K→+*K) (r r' : K)
    (hF : ∀x,i (A x)=F (i x))
    (hR : ∀x,i (R x)=d*i x*d⁻¹)
    (hR' : ∀x,i (R' x)=F d*i x*(F d)⁻¹)
    (hA : ∀x,p (A x)=sigma (p x))
    (hpR : ∀x,p (R x)=r*p x) (hpR' : ∀x,p (R' x)=r'*p x)
    (x : C) (hx : p x=1) : r'=sigma r := by
  have he : A (R x)=R' (A x) := by
    apply hi
    calc
      i (A (R x))=F (i (R x)) := hF _
      _=F (d*i x*d⁻¹) := congrArg F (hR x)
      _=F d*F (i x)*(F d)⁻¹ := by rw [map_mul,map_mul,map_inv]
      _=F d*i (A x)*(F d)⁻¹ := by rw [←hF]
      _=i (R' (A x)) := (hR' (A x)).symm
  have hh := congrArg p he
  simpa only [hA,hpR,hpR',hx,mul_one,map_one] using hh.symm

end SymmetricSubgroupAsymptotics.CFSGSemilinearConjugationCharacters
