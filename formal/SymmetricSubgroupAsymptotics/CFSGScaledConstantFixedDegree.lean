import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.Tactic.Ring

/-! A scaled Burnside bound on an ACTUAL finite permutation action.
When orbit and fixed-point counts share a factor a, constant nonidentity
fixed-point counts force degree at least a times the group order. This
supports Heisenberg orbit compression without constructing an artificial
action on a smaller carrier. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
open MulAction

theorem scaled_card_le_of_constant_fixedBy {P X : Type*} [Group P] [Finite P]
    [Finite X] [MulAction P X] (a f : ℕ) (ha : 0 < a)
    (hfix : ∀ g : P, g ≠ 1 → Nat.card (fixedBy X g) = f)
    (hmove : ∃ (g : P) (x : X), g • x ≠ x)
    (hdegree : a ∣ Nat.card X) (hfixed : a ∣ f)
    (horbits : a ∣ Nat.card (Quotient (orbitRel P X))) :
    a * Nat.card P ≤ Nat.card X := by
  letI : Fintype P := Fintype.ofFinite P
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (Quotient (orbitRel P X)) := Fintype.ofFinite _
  obtain ⟨n, hn⟩ := hdegree
  obtain ⟨b, hb⟩ := hfixed
  obtain ⟨c, hc⟩ := horbits
  have hn' : Fintype.card X = a * n := by
    simpa only [Nat.card_eq_fintype_card] using hn
  have hc' : Fintype.card (Quotient (orbitRel P X)) = a * c := by
    simpa only [Nat.card_eq_fintype_card] using hc
  obtain ⟨g, x, hgx⟩ := hmove
  have hg : g ≠ 1 := by
    rintro rfl
    exact hgx (one_smul P x)
  have hf : f < Fintype.card X := by
    rw [← hfix g hg, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_injective_of_notMem
      (fun y : fixedBy X g => y.val) Subtype.val_injective (b := x)
    rintro ⟨y, rfl⟩
    exact hgx y.property
  have hbn : b < n := by
    rw [hb, hn'] at hf
    exact Nat.lt_of_mul_lt_mul_left hf
  have hone : Fintype.card (fixedBy X (1 : P)) = Fintype.card X :=
    Fintype.card_congr
      { toFun := fun y => y.val
        invFun := fun y => ⟨y, one_smul P y⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun _ => rfl }
  have hsum : (∑ g : P, Fintype.card (fixedBy X g)) =
      Fintype.card X + (Fintype.card P - 1) * f := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : P)), hone]
    congr 1
    calc
      _ = ∑ g ∈ (Finset.univ : Finset P).erase 1, f := by
        apply Finset.sum_congr rfl
        intro g hg
        exact (Nat.card_eq_fintype_card (α := fixedBy X g)).symm.trans
          (hfix g (Finset.mem_erase.mp hg).1)
      _ = (Fintype.card P - 1) * f := by simp
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group P X
  rw [hsum, hn', hb, hc'] at hburn
  have hscaled : n + (Fintype.card P - 1) * b = c * Fintype.card P := by
    apply Nat.eq_of_mul_eq_mul_left ha
    calc
      a * (n + (Fintype.card P - 1) * b) =
          a * n + (Fintype.card P - 1) * (a * b) := by ring
      _ = (a * c) * Fintype.card P := hburn
      _ = a * (c * Fintype.card P) := by ring
  have hp : 1 ≤ Fintype.card P := Fintype.card_pos
  have hsplit : (Fintype.card P - 1) * b + b = Fintype.card P * b := by
    calc
      _ = ((Fintype.card P - 1) + 1) * b := by rw [Nat.add_mul, one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hp]
  have hdecomp : (n - b) + Fintype.card P * b =
      n + (Fintype.card P - 1) * b := by omega
  have hdiv : Fintype.card P ∣ n - b := by
    have hd : Fintype.card P ∣ (n - b) + Fintype.card P * b := by
      rw [hdecomp, hscaled]
      exact dvd_mul_left _ _
    have hh := Nat.dvd_sub hd (dvd_mul_right (Fintype.card P) b)
    simpa only [Nat.add_sub_cancel] using hh
  have hpn : Fintype.card P ≤ n :=
    (Nat.le_of_dvd (by omega : 0 < n - b) hdiv).trans (Nat.sub_le n b)
  calc
    a * Nat.card P = a * Fintype.card P := by rw [Nat.card_eq_fintype_card]
    _ ≤ a * n := Nat.mul_le_mul_left a hpn
    _ = Nat.card X := hn.symm

end SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
