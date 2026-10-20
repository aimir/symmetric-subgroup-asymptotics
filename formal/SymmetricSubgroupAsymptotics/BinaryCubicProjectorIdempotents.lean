import Mathlib.RepresentationTheory.Basic

/-! The two actual cubic projectors over F2 are idempotent. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCubicProjectorIdempotents
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem add_self (T : Module.End (ZMod 2) V) : T+T=0 := by
  ext v
  change T v+T v=0
  rw [← two_smul (ZMod 2),show (2 : ZMod 2)=0 by decide,zero_smul]

theorem active (T : Module.End (ZMod 2) V) (hc : T^3=1) : (T+T^2)^2=T+T^2 := by
  have h4 : T^4=T := by
    rw [show (4 : ℕ)=3+1 from rfl,pow_add,hc,pow_one,one_mul]
  have h11 : (1 : Module.End (ZMod 2) V)+1=0 := add_self 1
  have hAA : T*T=T^2 := (pow_two T).symm
  have hA2A : T^2*T=1 := by rw [← pow_succ,hc]
  have hAA2 : T*T^2=1 := by rw [← pow_succ',hc]
  have hA22 : T^2*T^2=T := by rw [← pow_add,h4]
  calc
    (T+T^2)^2=T^2+(1+1)+T := by
      rw [pow_two,add_mul,mul_add,mul_add,hAA,hAA2,hA2A,hA22]
      abel
    _=T+T^2 := by rw [h11,add_zero]; exact add_comm _ _

theorem fixed (T : Module.End (ZMod 2) V) (hc : T^3=1) :
    (1+T+T^2)^2=1+T+T^2 := by
  let F := T+T^2
  have hf : F^2=F := active T hc
  have hexpand : ∀ P : Module.End (ZMod 2) V, (1+P)^2=1+(P+P)+P^2 := by
    intro P
    rw [pow_two]
    simp only [add_mul,mul_add,one_mul,mul_one]
    rw [← pow_two]
    abel
  have he : (1+F)^2=1+F := by
    calc
      (1+F)^2=1+(F+F)+F^2 := hexpand F
      _=1+F := by rw [add_self,hf,add_zero]
  simpa only [F,add_assoc] using he

end SymmetricSubgroupAsymptotics.BinaryCubicProjectorIdempotents
