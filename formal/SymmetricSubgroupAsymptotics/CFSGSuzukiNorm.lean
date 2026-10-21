import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentArray
import SymmetricSubgroupAsymptotics.CFSGSuzukiFieldParameters

/-! The actual Suzuki norm and its anisotropy. The argument uses only
characteristic two and theta squared equal to Frobenius; no group order,
BN-pair, or model-recognition theorem is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiNorm
variable {K : Type*} [Field K] [CharP K 2]

def twistedNorm (t : K →+* K) (a b : K) : K := a^2*t a+a*b+t b

omit [CharP K 2] in
theorem theta_norm (t : K →+* K) (ht : ∀ x,t (t x)=x^2) (a b : K) :
    t (twistedNorm t a b)=(t a)^2*a^2+t a*t b+b^2 := by
  simp only [twistedNorm,map_add,map_mul,map_pow,ht]

/-- A small polynomial identity proves anisotropy without division. -/
theorem norm_discriminant (t : K →+* K) (ht : ∀ x,t (t x)=x^2) (a b : K) :
    b*(b+a*t a)=t (twistedNorm t a b)+t a*twistedNorm t a b := by
  rw [theta_norm t ht]
  dsimp only [twistedNorm]
  ring_nf <;> simp

theorem norm_diagonal (t : K →+* K) (ht : ∀ x,t (t x)=x^2) (a : K) :
    twistedNorm t a (a*t a)=a^2*t a := by
  simp only [twistedNorm,map_mul,ht]
  ring_nf
  simp

theorem twistedNorm_eq_zero_iff (t : K →+* K) (ht : ∀ x,t (t x)=x^2) (a b : K) :
    twistedNorm t a b=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro hz
    have hb : b*(b+a*t a)=0 := by rw [norm_discriminant t ht,hz,map_zero,mul_zero,zero_add]
    have haProduct : a^2*t a=0 := by
      rcases mul_eq_zero.mp hb with hb|hb
      · simpa only [twistedNorm,hb,map_zero,mul_zero,add_zero] using hz
      · have hba : b=a*t a := by
          have he := eq_neg_of_add_eq_zero_left hb
          simpa using he
        rw [hba,norm_diagonal t ht] at hz
        exact hz
    have ha : a=0 := by
      by_contra h
      have hta : t a≠0 := by
        intro he
        apply h
        apply t.injective
        simpa only [map_zero] using he
      exact (mul_ne_zero (pow_ne_zero 2 h) hta) haProduct
    refine ⟨ha,?_⟩
    apply t.injective
    simpa only [ha,twistedNorm,zero_pow (by decide : 2≠0),map_zero,zero_mul,zero_add] using hz
  · rintro ⟨rfl,rfl⟩
    simp [twistedNorm]

open CFSGSuzukiFieldParameters

def suzukiNorm (m : ℕ) (a b : Field m) : Field m := twistedNorm (theta m) a b

theorem suzukiNorm_eq_zero_iff (m : ℕ) (a b : Field m) :
    suzukiNorm m a b=0 ↔ a=0 ∧ b=0 :=
  twistedNorm_eq_zero_iff (theta m) (theta_twice m) a b

theorem suzukiNorm_ne_zero (m : ℕ) {a b : Field m} (hab : a≠0 ∨ b≠0) :
    suzukiNorm m a b≠0 := by
  intro hz
  obtain ⟨ha,hb⟩ := (suzukiNorm_eq_zero_iff m a b).mp hz
  rcases hab with h|h
  · exact h ha
  · exact h hb

@[simp] theorem unipotent_norm_entry (m : ℕ) (a b : Field m) :
    CFSG.Models.SuzukiConstruction.unipotent m a b 3 0=suzukiNorm m a b := rfl

end SymmetricSubgroupAsymptotics.CFSGSuzukiNorm
