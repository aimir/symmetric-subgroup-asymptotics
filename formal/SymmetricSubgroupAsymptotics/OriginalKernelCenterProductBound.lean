import SymmetricSubgroupAsymptotics.OriginalKernelCenter
import Mathlib.GroupTheory.QuotientGroup.Finite

/-! The centre of an actual extension is bounded by its actual fixed
kernel and actual quotient centre. No splitting or faithful kernel action
is assumed, and the quotient is not replaced by an unrelated model. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {k Q B : Type} [CommRing k] [Group Q] [Finite Q] [Group B] [Finite B]
    {pi : Q →* B} {A : Rep k B} (E : OriginalKernelModuleChart pi A)

include E in
/-- Both factors refer to the SAME actual extension. -/
theorem OriginalKernelModuleChart.center_card_le_invariants_mul_center
    (hpi : Function.Surjective pi) :
    Nat.card (Subgroup.center Q) ≤
      Nat.card A.ρ.invariants * Nat.card (Subgroup.center B) := by
  letI originalKernelCenterProduct_finiteA : Finite A :=
    Finite.of_injective E.element E.element_injective
  let f : Subgroup.center Q →* Subgroup.center B := {
    toFun z := ⟨pi z.val, Subgroup.mem_center_iff.mpr (by
      intro b
      obtain ⟨q, rfl⟩ := hpi b
      simpa only [map_mul] using congrArg pi ((Subgroup.mem_center_iff.mp z.property) q))⟩
    map_one' := Subtype.ext pi.map_one
    map_mul' x y := Subtype.ext (pi.map_mul x.val y.val) }
  have hk (x : f.ker) : pi (x.val.val : Q) = 1 :=
    congrArg (fun z : Subgroup.center B => (z : B)) x.property
  let a (x : f.ker) : A := (E.equiv.symm ⟨x.val.val, hk x⟩).toAdd
  have ha (x : f.ker) : E.element (a x) = (x.val.val : Q) :=
    congrArg (fun z : pi.ker => (z : Q))
      (E.equiv.apply_symm_apply ⟨x.val.val, hk x⟩)
  let j : f.ker → A.ρ.invariants := fun x => ⟨a x,
    (E.element_mem_center_iff hpi (a x)).mp ((ha x).symm ▸ x.val.property)⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg (fun v : A.ρ.invariants => E.element (v : A)) h
    exact (ha x).symm.trans (he.trans (ha y))
  have hc := f.ker.card_eq_card_quotient_mul_card_subgroup
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hc
  calc
    Nat.card (Subgroup.center Q) = Nat.card f.ker * Nat.card f.range := hc.trans (Nat.mul_comm _ _)
    _ ≤ Nat.card A.ρ.invariants * Nat.card (Subgroup.center B) :=
      Nat.mul_le_mul (Nat.card_le_card_of_injective j hj) (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective)

end SymmetricSubgroupAsymptotics
