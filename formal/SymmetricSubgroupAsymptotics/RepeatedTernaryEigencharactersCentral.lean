import SymmetricSubgroupAsymptotics.IrreducibleCommutingEigenvalue
import SymmetricSubgroupAsymptotics.TernaryRepeatedDiagonalTrace
import SymmetricSubgroupAsymptotics.SeparatedEigenbasisMonomial
import Mathlib.LinearAlgebra.Trace

/-! On an irreducible ternary three-space, a normal diagonal subgroup
cannot have a repeated joint character unless all its operators are
scalar. A tiny diagonal trace receipt makes each nonscalar operator
central; its actual eigenvector then forces it to be scalar. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.RepeatedTernaryEigencharactersCentral
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 3) V]
    (rho : Representation (ZMod 3) G V)
    (b : Module.Basis (Fin 3) (ZMod 3) V)
    (N : Subgroup G) [N.Normal] (a : N → Fin 3 → ZMod 3)
    (heigen : ∀ (n : N) (i : Fin 3),rho n.val (b i)=a n i • b i)

include heigen

omit [N.Normal] in
theorem eigenvalue_ne_zero (n : N) (i : Fin 3) : a n i≠0 := by
  intro hz
  have h := congrArg (rho n.val⁻¹) (heigen n i)
  rw [hz,zero_smul,map_zero] at h
  have he : rho n.val⁻¹ (rho n.val (b i))=b i := by
    change (rho n.val⁻¹*rho n.val) (b i)=b i
    rw [←map_mul,inv_mul_cancel,map_one]
    rfl
  rw [he] at h
  exact b.ne_zero i h

omit [N.Normal] in
theorem trace_eq_sum (n : N) :
    LinearMap.trace (ZMod 3) V (rho n.val)=∑ i,a n i := by
  rw [LinearMap.trace_eq_matrix_trace (ZMod 3) b]
  change (∑ i,LinearMap.toMatrix b b (rho n.val) i i)=∑ i,a n i
  apply Finset.sum_congr rfl
  intro i _
  simp [LinearMap.toMatrix_apply,heigen,Module.Basis.repr_self_apply]

theorem scalar_of_repeated_character
    (hrho : Representation.IsIrreducible rho)
    (i j : Fin 3) (hij : i≠j) (hrepeat : ∀ n : N,a n i=a n j) :
    ∀ (n : N) (t : Fin 3),a n t=a n 0 := by
  intro n
  by_cases hconst : ∀ t : Fin 3,a n t=a n 0
  · exact hconst
  · have hconj (g : G) : rho (g*n.val*g⁻¹)=rho n.val := by
      let m : N := ⟨g*n.val*g⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : N.Normal) n.val n.property g⟩
      have htrace : LinearMap.trace (ZMod 3) V (rho m.val)=
          LinearMap.trace (ZMod 3) V (rho n.val) := by
        change LinearMap.trace (ZMod 3) V (rho (g*n.val*g⁻¹))=_
        rw [map_mul rho,map_mul rho,LinearMap.trace_mul_cycle]
        simp only [←map_mul rho,inv_mul_cancel,one_mul]
      have ha : a n=a m := TernaryRepeatedDiagonalTrace.separation_receipt i j
        (a n) (a m) hij (eigenvalue_ne_zero rho b N a heigen n)
        (eigenvalue_ne_zero rho b N a heigen m) (hrepeat n) (hrepeat m)
        hconst (by
          rw [←trace_eq_sum rho b N a heigen n,←trace_eq_sum rho b N a heigen m]
          exact htrace.symm)
      apply b.ext
      intro t
      change rho m.val (b t)=rho n.val (b t)
      rw [heigen,heigen,congrFun ha t]
    have hcomm (g : G) (v : V) : rho n.val (rho g v)=rho g (rho n.val v) := by
      have he := congrArg (fun f : Module.End (ZMod 3) V => f*rho g) (hconj g)
      have hm : rho g*rho n.val=rho n.val*rho g := by
        simpa only [←map_mul,mul_assoc,inv_mul_cancel,mul_one] using he
      exact congrArg (fun f : Module.End (ZMod 3) V => f v) hm.symm
    have hscalar := IrreducibleCommutingEigenvalue.apply_eq_smul_of_eigenvector
      rho hrho (rho n.val) (a n 0) hcomm (b 0) (b.ne_zero 0) (heigen n 0)
    intro t
    have he := (heigen n t).symm.trans (hscalar (b t))
    have hc := congrArg (fun v : V => b.repr v t) he
    simpa [Module.Basis.repr_self_apply] using hc

theorem separated_of_nonscalar
    (hrho : Representation.IsIrreducible rho)
    (hnonscalar : ∃ (n : N) (t : Fin 3),a n t≠a n 0) :
    ∀ i j : Fin 3,i≠j → ∃ n : N,a n i≠a n j := by
  intro i j hij
  by_contra h
  have heq : ∀ n : N,a n i=a n j := fun n => not_not.mp (not_exists.mp h n)
  obtain ⟨n,t,ht⟩ := hnonscalar
  exact ht (scalar_of_repeated_character rho b N a heigen hrho i j hij heq n t)

end SymmetricSubgroupAsymptotics.RepeatedTernaryEigencharactersCentral
