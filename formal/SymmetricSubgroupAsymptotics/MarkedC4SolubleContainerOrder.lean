import SymmetricSubgroupAsymptotics.MarkedC4SolubleContainerCount

/-! The order of the ACTUAL physical containers, using only Dixon's
published ordinary soluble permutation-group bound, quoted as RDT
Theorem 8.6(ii), p.34. No container group, code, or marked inequality is
part of that literature hypothesis. The product action and its cover were
constructed from literal original orbit fibres in the preceding module. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.SolubleContainerOrder
open LiteralSolubleOrbitContainers SolubleContainerCount

/-- Dixon's |H| ≤ 24^(n/3), for an ordinary soluble permutation group. -/
def PublishedDixonOrder : Prop :=
  ∀ (X : Type) [Fintype X] (H : Subgroup (Equiv.Perm X)) [IsSolvable H],
    (Nat.card H : ℝ) ≤ (24 : ℝ)^((Fintype.card X : ℝ)/3)

theorem factor_order (hDixon : PublishedDixonOrder)
    (X : Type) [Fintype X] (H : Subgroup (Equiv.Perm X)) [IsSolvable H] :
    Nat.card H ≤ 2^(2*Fintype.card X) := by
  have h : (Nat.card H : ℝ) ≤ (2 : ℝ)^(2*(Fintype.card X : ℝ)) := by
    calc
      _ ≤ (24 : ℝ)^((Fintype.card X : ℝ)/3) := hDixon X H
      _ ≤ (64 : ℝ)^((Fintype.card X : ℝ)/3) :=
        Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
      _ = (2 : ℝ)^(2*(Fintype.card X : ℝ)) := by
        rw [show (64 : ℝ) = (2 : ℝ)^(6 : ℝ) by norm_num,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring
  exact_mod_cast h

variable (X : Type) [Fintype X]

def physicalContainer (i : Index X) : Subgroup (Equiv.Perm X) := container i.1 i.2

theorem physicalContainer_order (hDixon : PublishedDixonOrder) (i : Index X) :
    Nat.card (physicalContainer X i) ≤ 2^(2*Fintype.card X) := by
  letI (j : X) : Fintype (i.2 j).val := Fintype.ofFinite _
  have hfactor (j : X) : Fintype.card (i.2 j).val ≤
      2^(2*Fintype.card (Fiber i.1 j)) := by
    letI : IsSolvable (i.2 j).val := (i.2 j).property.1.1
    simpa only [Nat.card_eq_fintype_card] using
      factor_order hDixon (Fiber i.1 j) (i.2 j).val
  calc
    Nat.card (physicalContainer X i) ≤ Nat.card (∀ j : X, (i.2 j).val) :=
      Nat.card_le_card_of_surjective (physicalMap i.1 i.2).rangeRestrict
        (physicalMap i.1 i.2).rangeRestrict_surjective
    _ = ∏ j : X, Fintype.card (i.2 j).val := by
      rw [Nat.card_eq_fintype_card,Fintype.card_pi]
    _ ≤ ∏ j : X, 2^(2*Fintype.card (Fiber i.1 j)) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hfactor j)
    _ = 2^(2*Fintype.card X) := by
      rw [Finset.prod_pow_eq_pow_sum,← Finset.mul_sum,fiber_sum]

/-- The original soluble subgroup, including all point labels, has a
container in the counted menu. This is a proved cover, not an input. -/
theorem cover (H : Subgroup (Equiv.Perm X)) [IsSolvable H] :
    ∃ i : Index X, H ≤ physicalContainer X i := by
  obtain ⟨D,hD⟩ := exists_container H
  exact ⟨⟨orbitLabel H,D⟩,hD⟩

end SymmetricSubgroupAsymptotics.MarkedC4.SolubleContainerOrder
end
