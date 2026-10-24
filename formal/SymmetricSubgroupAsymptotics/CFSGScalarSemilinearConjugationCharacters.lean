import SymmetricSubgroupAsymptotics.CFSGSemilinearConjugationCharacters
import Mathlib.Algebra.Field.Basic

/-! Scalar-semilinear first coordinates transport conjugation characters
by the field map: the nonzero scalar coefficient cancels. The coordinate
object may be a nonabelian unipotent group. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGScalarSemilinearConjugationCharacters

theorem character_eq_of_scalar_semilinear_conjugation {G C K : Type*} [Group G] [Field K]
    (i : C→G) (hi : Function.Injective i) (F : MulAut G) (A R R' : C→C)
    (d : G) (p : C→K) (sigma : K→+*K) (r r' c : K) (hc : c≠0)
    (hF : ∀x,i (A x)=F (i x))
    (hR : ∀x,i (R x)=d*i x*d⁻¹)
    (hR' : ∀x,i (R' x)=F d*i x*(F d)⁻¹)
    (hA : ∀x,p (A x)=c*sigma (p x))
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
  have hscalar : c*sigma r=r'*c := by
    simpa only [hA,hpR,hpR',hx,mul_one,map_one] using hh
  exact mul_left_cancel₀ hc ((mul_comm c r').trans hscalar.symm)

end SymmetricSubgroupAsymptotics.CFSGScalarSemilinearConjugationCharacters
