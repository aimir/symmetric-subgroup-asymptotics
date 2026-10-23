import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Group

/-! A lower bound from independently separated ACTUAL coset charts.
No chart surjectivity or normal-form assertion is required. This lets
fixed root-orbit products be collected by height without assuming that
an arbitrarily ordered full root word is diagram invariant. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourFilteredChartCardinality
variable {G : Type*} [Group G] [Finite G]

theorem chart_mul_card_le {C : Type*} [Finite C]
    (A B : Subgroup G) (hle : B≤A) (w : C→A)
    (hsep : ∀c d,(w c : G)⁻¹*(w d : G)∈B→c=d) :
    Nat.card C * Nat.card B≤Nat.card A := by
  let f : C×B→A := fun p=>w p.1*⟨p.2.val,hle p.2.property⟩
  have hf : Function.Injective f := by
    rintro ⟨c,b⟩ ⟨d,e⟩ he
    have hv := congrArg (fun a : A=>a.val) he
    change (w c : G)*b.val=(w d : G)*e.val at hv
    have hquot : (w c : G)⁻¹*(w d : G)=b.val*e.val⁻¹ := by
      calc
        (w c : G)⁻¹*(w d : G) =
            (w c : G)⁻¹*((w d : G)*e.val)*e.val⁻¹ := by group
        _=(w c : G)⁻¹*((w c : G)*b.val)*e.val⁻¹ := by rw [←hv]
        _=b.val*e.val⁻¹ := by group
    have hcd : c=d := hsep c d (by
      rw [hquot]
      exact B.mul_mem b.property (B.inv_mem e.property))
    subst d
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel hv))
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hf

theorem filtered_chart_card_lower (N : ℕ→Subgroup G) (C : ℕ→Type*)
    [∀n,Finite (C n)] (hle : ∀n,N (n+1)≤N n) (w : ∀n,C n→N n)
    (hsep : ∀n c d,(w n c : G)⁻¹*(w n d : G)∈N (n+1)→c=d)
    (m : ℕ) : (∏n∈Finset.range m,Nat.card (C n))≤Nat.card (N 0) := by
  have hstep (n : ℕ) : Nat.card (C n)*Nat.card (N (n+1))≤Nat.card (N n) :=
    chart_mul_card_le (N n) (N (n+1)) (hle n) (w n) (hsep n)
  have htel : ∀k,(∏n∈Finset.range k,Nat.card (C n))*Nat.card (N k)≤Nat.card (N 0) := by
    intro k
    induction k with
    | zero=>simp
    | succ k ih=>
      rw [Finset.prod_range_succ,mul_assoc]
      exact le_trans (Nat.mul_le_mul_left _ (hstep k)) ih
  have hpos : 1≤Nat.card (N m) := Nat.card_pos
  exact le_trans (by simpa only [mul_one] using
    Nat.mul_le_mul_left (∏n∈Finset.range m,Nat.card (C n)) hpos) (htel m)

end SymmetricSubgroupAsymptotics.CFSGFFourFilteredChartCardinality
