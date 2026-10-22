import SymmetricSubgroupAsymptotics.CFSGIntegralGramFinite
import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPairing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Finiteness of norm-two lattice roots from an actual denominator-cleared
rectangular Gram factor. No root list is supplied. -/
set_option autoImplicit false
set_option Elab.async false
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGIntegralGramRootFiniteness
open CFSGIntegerMatrixPairing
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

theorem gram_energy (A : Matrix n n ℤ) (T : Matrix m n ℤ) (d : ℕ)
    (hg : T.transpose*T=(d:ℤ) • A) (x : n→ℤ) :
    (∑ i,(T*ᵥx) i^2)=(d:ℤ)*integerPairing A x x := by
  calc
    (∑ i,(T*ᵥx) i^2)=(T*ᵥx) ⬝ᵥ(T*ᵥx) := by simp only [dotProduct,pow_two]
    _=((T*ᵥx) ᵥ* T) ⬝ᵥx := Matrix.dotProduct_mulVec _ _ _
    _=(T.transpose*ᵥ(T*ᵥx)) ⬝ᵥx := by rw [Matrix.mulVec_transpose]
    _=x ⬝ᵥ((T.transpose*T)*ᵥx) := by rw [Matrix.mulVec_mulVec,dotProduct_comm]
    _=(d:ℤ)*integerPairing A x x := by
      rw [hg,Matrix.smul_mulVec,dotProduct_smul]
      simp only [integerPairing,Matrix.toBilin'_apply',smul_eq_mul]

theorem gram_mulVec_injective (A : Matrix n n ℤ) (T : Matrix m n ℤ) (d : ℕ)
    (hd : 0 < d) (hg : T.transpose*T=(d:ℤ) • A)
    (hp : (rationalMatrix A).PosDef) : Function.Injective T.mulVec := by
  have hker : ∀ x:n→ℤ,T*ᵥx=0 → x=0 := by
    intro x hx
    have he := gram_energy A T d hg x
    rw [hx] at he
    simp only [Pi.zero_apply,zero_pow (by decide : 2≠0),Finset.sum_const_zero] at he
    have hd0 : (d:ℤ)≠0 := by exact_mod_cast (Nat.ne_of_gt hd)
    have hn : integerPairing A x x=0 := (mul_eq_zero.mp he.symm).resolve_left hd0
    by_contra hne
    have hcx : castVector x≠0 := by
      intro h
      apply hne
      apply castVector_injective
      simpa [castVector] using h
    have hpos := hp.dotProduct_mulVec_pos hcx
    have hz : star (castVector x) ⬝ᵥ(rationalMatrix A*ᵥcastVector x)=0 := by
      have hz' : rationalPairing A (castVector x) (castVector x)=0 := by
        rw [cast_pairing,hn]
        norm_num
      simpa only [rationalPairing,Matrix.toBilin'_apply',star_trivial] using hz'
    exact (ne_of_gt hpos) hz
  intro x y h
  apply sub_eq_zero.mp
  apply hker
  rw [Matrix.mulVec_sub,h,sub_self]

theorem finite_norm_two (A : Matrix n n ℤ) (T : Matrix m n ℤ) (d : ℕ)
    (hd : 0 < d) (hg : T.transpose*T=(d:ℤ) • A)
    (hp : (rationalMatrix A).PosDef) :
    {x:n→ℤ | integerPairing A x x=2}.Finite := by
  apply (CFSGIntegralGramFinite.finite_energy_level T
    (gram_mulVec_injective A T d hd hg hp) (2*d)).subset
  intro x hx
  change (∑ i,(T*ᵥx) i^2)=((2*d:ℕ):ℤ)
  rw [gram_energy A T d hg x,hx]
  push_cast
  ring

end SymmetricSubgroupAsymptotics.CFSGIntegralGramRootFiniteness
