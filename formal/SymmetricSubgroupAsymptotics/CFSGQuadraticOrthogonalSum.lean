import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
import Mathlib.Tactic.Abel

/-! Combining two commuting quadratic roots with orthogonal second columns.
All division is confined to the characteristic-zero rational verification;
the resulting second coefficient is the integral polynomial d+h+e*f. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGQuadraticOrthogonalSum
variable {R : Type*} [Ring R] [Algebra ℚ R]

private theorem cancel_two {x : R} (h : (2:ℚ) • x=0) : x=0 :=
  (smul_eq_zero.mp h).resolve_left (by norm_num)

theorem second_mul_other (e f d : R) (hc : Commute e f)
    (he : e*e=d+d) (hfd : f*d=0) : d*f=0 := by
  apply cancel_two
  calc
    (2:ℚ) • (d*f)=(d+d)*f := by rw [two_smul,add_mul]
    _=(e*e)*f := by rw [he]
    _=f*(e*e) := by simpa only [pow_two] using (hc.pow_left 2).eq
    _=f*(d+d) := by rw [he]
    _=0 := by rw [mul_add,hfd,zero_add]

theorem identities (e f d h : R) (hc : Commute e f)
    (he : e*e=d+d) (hf : f*f=h+h)
    (hed : e*d=0) (hde : d*e=0) (hfh : f*h=0) (hhf : h*f=0)
    (heh : e*h=0) (hfd : f*d=0) :
    (e+f)*(e+f)=(d+h+e*f)+(d+h+e*f) ∧
      (e+f)*(d+h+e*f)=0 ∧ (d+h+e*f)*(e+f)=0 ∧
      (d+h+e*f)*(d+h+e*f)=0 := by
  have hdf : d*f=0 := second_mul_other e f d hc he hfd
  have hhe : h*e=0 := second_mul_other f e h hc.symm hf heh
  have heef : e*(e*f)=0 := by rw [←mul_assoc,he,add_mul,hdf,zero_add]
  have hfef : f*(e*f)=0 := by
    rw [←mul_assoc,←hc.eq,mul_assoc,hf,mul_add,heh,zero_add]
  have hefe : (e*f)*e=0 := by
    rw [mul_assoc,←hc.eq,←mul_assoc,he,add_mul,hdf,zero_add]
  have heff : (e*f)*f=0 := by rw [mul_assoc,hf,mul_add,heh,zero_add]
  have hsquare : (e+f)*(e+f)=(d+h+e*f)+(d+h+e*f) := by
    rw [add_mul,mul_add,mul_add,he,hf,hc.eq]
    abel
  have hleft : (e+f)*(d+h+e*f)=0 := by
    simp only [add_mul,mul_add,hed,heh,hfd,hfh,heef,hfef,zero_add,add_zero]
  have hright : (d+h+e*f)*(e+f)=0 := by
    simp only [add_mul,mul_add,hde,hdf,hhe,hhf,hefe,heff,zero_add,add_zero]
  refine ⟨hsquare,hleft,hright,?_⟩
  apply cancel_two
  calc
    (2:ℚ) • ((d+h+e*f)*(d+h+e*f))=
        ((d+h+e*f)+(d+h+e*f))*(d+h+e*f) := by simp only [two_smul,add_mul]
    _=((e+f)*(e+f))*(d+h+e*f) := by rw [hsquare]
    _=0 := by rw [mul_assoc,hleft,mul_zero]

end SymmetricSubgroupAsymptotics.CFSGQuadraticOrthogonalSum
