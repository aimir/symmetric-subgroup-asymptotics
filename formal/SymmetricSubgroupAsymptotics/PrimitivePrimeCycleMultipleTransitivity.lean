import Mathlib.GroupTheory.GroupAction.Jordan

/-! Marggraff's prime-cycle consequence of the PROVED technical Jordan
criterion. This does not invoke the unproved general prime-cycle
alternating-containment declaration at the end of the Mathlib module. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitivePrimeCycleMultipleTransitivity
open MulAction

theorem isMultiplyPretransitive {n p k : ℕ}
    (J : Subgroup (Equiv.Perm (Fin n))) (hJ : MulAction.IsPreprimitive J (Fin n))
    (hp : p.Prime) (hdegree : n=p+(k+1))
    (g : Equiv.Perm (Fin n)) (hcycle : g.IsCycle) (hsupport : g.support.card=p)
    (hg : g∈J) : MulAction.IsMultiplyPretransitive J (Fin n) (k+2) := by
  classical
  have htotal := Set.ncard_add_ncard_compl (g.support : Set (Fin n))
  simp only [Set.ncard_coe_finset,Nat.card_fin] at htotal
  have hfixed : (g.supportᶜ : Set (Fin n)).ncard=k+1 := by omega
  have hsmall : k+2<Nat.card (Fin n) := by
    rw [Nat.card_fin]
    have hp2 := hp.two_le
    omega
  have hprimitive : MulAction.IsMultiplyPreprimitive J (Fin n) (k+2) := by
    apply hJ.isMultiplyPreprimitive hfixed hsmall
    have := Equiv.Perm.isPretransitive_of_isCycle_mem hcycle hg
    apply MulAction.IsPreprimitive.of_prime_card
    letI : Fintype (SubMulAction.ofFixingSubgroup J (g.supportᶜ : Set (Fin n))) :=
      Fintype.ofFinite _
    convert! hp
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,←hsupport]
    apply congr_arg
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  letI : MulAction.IsMultiplyPreprimitive J (Fin n) (k+2) := hprimitive
  infer_instance

end SymmetricSubgroupAsymptotics.PrimitivePrimeCycleMultipleTransitivity
