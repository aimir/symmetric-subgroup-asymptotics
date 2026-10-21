import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.SetTheory.Cardinal.Finite

/-! A faithful transitive nonabelian action has centre strictly smaller
than its point set. The same evaluation map proves both assertions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X]

theorem transitive_center_evaluation_injective (x : X) :
    Function.Injective (fun z : Subgroup.center G => (z : G) • x) := by
  intro a b he
  change (a : G) • x=(b : G) • x at he
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := X)
  intro y
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
  calc
    (a : G) • y = (a : G) • (g • x) := by rw [hg]
    _ = g • ((a : G) • x) := by
      rw [←mul_smul,←Subgroup.mem_center_iff.mp a.property g,mul_smul]
    _ = g • ((b : G) • x) := by rw [he]
    _ = (b : G) • (g • x) := by
      rw [←mul_smul,Subgroup.mem_center_iff.mp b.property g,mul_smul]
    _ = (b : G) • y := by rw [hg]

theorem transitive_nonabelian_center_card_lt [Finite G] [Finite X]
    (x : X) (hnonab : ¬∀ a b : G,a*b=b*a) :
    Nat.card (Subgroup.center G)<Nat.card X := by
  let ev : Subgroup.center G → X := fun z => (z : G) • x
  have hinj : Function.Injective ev := transitive_center_evaluation_injective x
  have hle : Nat.card (Subgroup.center G)≤Nat.card X := Nat.card_le_card_of_injective ev hinj
  by_contra hlt
  have heq : Nat.card (Subgroup.center G)=Nat.card X := le_antisymm hle (Nat.le_of_not_gt hlt)
  have hsurj : Function.Surjective ev :=
    ((Nat.bijective_iff_injective_and_card ev).mpr ⟨hinj,heq⟩).2
  have hall (g : G) : g∈Subgroup.center G := by
    obtain ⟨z,hz⟩ := hsurj (g • x)
    have hzG : (z : G)=g := by
      apply eq_of_smul_eq_smul (α := X)
      intro y
      obtain ⟨a,ha⟩ := hsurj y
      change (a : G) • x=y at ha
      change (z : G) • x=g • x at hz
      calc
        (z : G) • y = ((z : G)*(a : G)) • x := by rw [ha.symm,mul_smul]
        _ = ((a : G)*(z : G)) • x := by rw [Subgroup.mem_center_iff.mp a.property]
        _ = (a : G) • (g • x) := by rw [mul_smul,hz]
        _ = (g*(a : G)) • x := by
          rw [←mul_smul,←Subgroup.mem_center_iff.mp a.property g]
        _ = g • y := by rw [mul_smul,ha]
    rw [←hzG]
    exact z.property
  exact hnonab (fun a b => Subgroup.mem_center_iff.mp (hall b) a)

end SymmetricSubgroupAsymptotics
