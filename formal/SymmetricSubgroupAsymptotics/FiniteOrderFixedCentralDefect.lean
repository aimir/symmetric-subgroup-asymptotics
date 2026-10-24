import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Group

/-! A fixed additive-field defect cannot survive an automorphism whose
order is invertible in that field. This proves actual fixedness of a
given lift; no canonical section, quotient-fixed lifting assumption or
centrality hypothesis is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteOrderFixedCentralDefect

theorem fixed_of_fixed_defect {G : Type*} [Group G]
    (T : MulAut G) (n : ℕ) (hT : T^n=1) (x d : G)
    (hd : T x=d*x) (hfix : T d=d) (htorsion : d^n=1 → d=1) : T x=x := by
  have hi (i : ℕ) : (T^i) x=d^i*x := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ']
      change T ((T^i) x)=d^(i+1)*x
      rw [ih,map_mul,map_pow,hfix,hd,pow_succ']
      group
  have hn : d^n=1 := by
    have he := hi n
    rw [hT] at he
    change x=d^n*x at he
    exact mul_right_cancel (he.symm.trans (one_mul x).symm)
  rw [htorsion hn,one_mul] at hd
  exact hd

theorem fixed_of_field_defect {G K : Type*} [Group G] [Field K]
    (T : MulAut G) (n : ℕ) (hT : T^n=1) (hn : (n : K)≠0)
    (z : Multiplicative K →* G) (hz : Function.Injective z)
    (hfix : ∀ a, T (z a)=z a) (x : G)
    (hdefect : T x*x⁻¹ ∈ z.range) : T x=x := by
  obtain ⟨a,ha⟩ := hdefect
  have hd : T x=z a*x := by
    rw [ha]
    group
  apply fixed_of_fixed_defect T n hT x (z a) hd (hfix a)
  intro hp
  have hap : a^n=1 := hz (by simpa only [map_pow,map_one] using hp)
  have hzero : (n : K)*a.toAdd=0 := by
    have h := congrArg Multiplicative.toAdd hap
    simpa only [toAdd_pow,toAdd_one,nsmul_eq_mul] using h
  have ha0 : a.toAdd=0 := (mul_eq_zero.mp hzero).resolve_left hn
  have ha1 : a=1 := congrArg Multiplicative.ofAdd ha0
  rw [ha1,map_one]

end SymmetricSubgroupAsymptotics.FiniteOrderFixedCentralDefect
