import SymmetricSubgroupAsymptotics.PrimeKernelFrobeniusSubgroupClassBound
import SymmetricSubgroupAsymptotics.PrimeCardAutomorphismAction
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.QuadraticOrderClassNumerics
import Mathlib.Tactic.IntervalCases

/-! Every subgroup of an ACTUAL prime-degree affine profile has at most
the ambient degree many classes. The checked Frobenius difference/count
and actual subgroup projection dichotomy discharge all hypotheses. This
includes degrees five and seven without group catalogue rows. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimeDegreeAffineAllSubgroupsClassBound

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] (P : PrimitiveAffineProfile G X)

include P in
theorem subgroup_class_card_le_degree (x : X) (hp : Nat.Prime (Nat.card X))
    (H : Subgroup G) : Nat.card (ConjClasses H) ≤ Nat.card X := by
  letI : Fact (Nat.card P.V).Prime := ⟨by rw [P.card_eq x]; exact hp⟩
  letI : IsCyclic P.V := isCyclic_of_prime_card (p := Nat.card P.V) rfl
  letI : CommGroup P.V := inferInstance
  letI : Nontrivial P.V := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [P.card_eq x]; exact hp.one_lt)
  letI : IsMulCommutative (P.complement x) :=
    PrimeCardAutomorphismAction.faithful_action_isMulCommutative
      (P.complementAction x) (P.complementAction_injective x)
  letI : CommGroup (P.complement x) := inferInstance
  let e : P.V ⋊[P.complementAction x] P.complement x ≃* G := P.semidirectEquiv x
  letI : Finite (P.V ⋊[P.complementAction x] P.complement x) :=
    Finite.of_equiv G e.symm.toEquiv
  let L := H.map e.symm.toMonoidHom
  let a : H ≃* L := e.symm.subgroupMap H
  have hc : Nat.card (ConjClasses H) ≤ Nat.card (ConjClasses L) :=
    Nat.card_le_card_of_surjective (ConjClasses.map a.symm.toMonoidHom)
      (ConjClasses.map_surjective a.symm.surjective)
  have hfree := PrimeCardAutomorphismAction.faithful_action_free
    (P.complementAction x) (P.complementAction_injective x)
  exact (hc.trans (PrimeKernelFrobeniusSubgroupClassBound.subgroup_class_card_le_kernel
    (P.complementAction x) hfree L)).trans_eq (P.card_eq x)

private theorem degree_cube_le (n : ℕ) (hn : 4 ≤ n) : n^3 ≤ 5^(n-1) := by
  by_cases h10 : 10 ≤ n
  · exact (Nat.pow_le_pow_right (by omega : 0 < n) (by decide : 3 ≤ 6)).trans
      (QuadraticOrderClassNumerics.sixth_power_le_garonziMaroti n h10)
  · interval_cases n <;> norm_num

include P in
theorem subgroup_class_cube_le_garonziMaroti (x : X)
    (hp : Nat.Prime (Nat.card X)) (hn : 4 ≤ Nat.card X) (H : Subgroup G) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) :=
  (Nat.pow_le_pow_left (subgroup_class_card_le_degree P x hp H) 3).trans
    (degree_cube_le (Nat.card X) hn)

end SymmetricSubgroupAsymptotics.PrimeDegreeAffineAllSubgroupsClassBound
