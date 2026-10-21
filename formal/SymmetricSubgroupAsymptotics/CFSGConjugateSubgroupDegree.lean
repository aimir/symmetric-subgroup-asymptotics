import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.FixedPoints
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-! A Burnside degree bound: if all nonidentity members of a subgroup
are conjugate in the ambient group, any nontrivial permutation action
of that subgroup has degree at least its order. This uses the literal
action and fixed-point counts, rather than an abstract rank estimate. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
open MulAction

theorem card_le_of_constant_fixedBy {P X : Type*} [Group P] [Finite P]
    [Finite X] [MulAction P X] (f : ℕ)
    (hfix : ∀ g : P, g ≠ 1 → Nat.card (fixedBy X g) = f)
    (hmove : ∃ (g : P) (x : X), g • x ≠ x) : Nat.card P ≤ Nat.card X := by
  letI : Fintype P := Fintype.ofFinite P
  letI : Fintype X := Fintype.ofFinite X
  letI : Fintype (Quotient (orbitRel P X)) := Fintype.ofFinite _
  obtain ⟨g,x,hgx⟩ := hmove
  have hg : g ≠ 1 := by rintro rfl; exact hgx (one_smul P x)
  have hf : f < Fintype.card X := by
    rw [← hfix g hg, Nat.card_eq_fintype_card]
    apply Fintype.card_lt_of_injective_of_notMem
      (fun y : fixedBy X g => y.val) Subtype.val_injective (b := x)
    rintro ⟨y,rfl⟩
    exact hgx y.property
  have hone : Fintype.card (fixedBy X (1 : P)) = Fintype.card X := by
    exact Fintype.card_congr
      { toFun := fun y => y.val
        invFun := fun y => ⟨y,one_smul P y⟩
        left_inv := fun y => Subtype.ext rfl
        right_inv := fun _ => rfl }
  have hsum : (∑ a : P, Fintype.card (fixedBy X a)) =
      Fintype.card X + (Fintype.card P - 1) * f := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : P)),hone]
    congr 1
    calc
      _ = ∑ a ∈ (Finset.univ : Finset P).erase 1, f := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (Nat.card_eq_fintype_card (α := fixedBy X a)).symm.trans
          (hfix a (Finset.mem_erase.mp ha).1)
      _ = (Fintype.card P - 1) * f := by simp
  have hburn := sum_card_fixedBy_eq_card_orbits_mul_card_group P X
  rw [hsum] at hburn
  have hq : 1 ≤ Fintype.card P := Fintype.card_pos
  have hsplit : (Fintype.card P - 1) * f + f = Fintype.card P * f := by
    calc
      _ = ((Fintype.card P - 1) + 1) * f := by rw [Nat.add_mul,one_mul]
      _ = _ := by rw [Nat.sub_add_cancel hq]
  have hdecomp : (Fintype.card X - f) + Fintype.card P * f =
      Fintype.card X + (Fintype.card P - 1) * f := by omega
  have hd : Fintype.card P ∣ (Fintype.card X - f) + Fintype.card P * f := by
    rw [hdecomp,hburn]
    exact dvd_mul_left _ _
  have hdiv : Fintype.card P ∣ Fintype.card X - f := by
    have h := Nat.dvd_sub hd (dvd_mul_right (Fintype.card P) f)
    simpa only [Nat.add_sub_cancel] using h
  have hle := Nat.le_of_dvd (by omega : 0 < Fintype.card X - f) hdiv
  simpa only [Nat.card_eq_fintype_card] using
    hle.trans (Nat.sub_le (Fintype.card X) f)

def fixedByConjugateEquiv {G X : Type*} [Group G] [MulAction G X]
    (a g : G) : fixedBy X a ≃ fixedBy X (g*a*g⁻¹) where
  toFun x := ⟨g • x.val,by
    change (g*a*g⁻¹) • (g • x.val) = g • x.val
    simp only [mul_smul,inv_smul_smul]
    exact congrArg (fun z : X => g • z) x.property⟩
  invFun x := ⟨g⁻¹ • x.val,by
    have hx := congrArg (fun z : X => g⁻¹ • z) x.property
    simpa only [mul_smul,inv_smul_smul] using hx⟩
  left_inv x := Subtype.ext (inv_smul_smul g x.val)
  right_inv x := Subtype.ext (smul_inv_smul g x.val)

theorem card_le_of_nonidentity_conjugate {G X : Type*} [Group G]
    [MulAction G X] [Finite X] (E : Subgroup G) [Finite E]
    (hconj : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      ∃ g : G, g*(a : G)*g⁻¹=(b : G))
    (hmove : ∃ (a : E) (x : X), (a : G) • x ≠ x) :
    Nat.card E ≤ Nat.card X := by
  obtain ⟨a,x,hax⟩ := hmove
  have ha : a ≠ 1 := by
    rintro rfl
    exact hax (one_smul G x)
  apply card_le_of_constant_fixedBy (Nat.card (fixedBy X a)) ?_
    ⟨a,x,hax⟩
  intro b hb
  obtain ⟨g,hg⟩ := hconj a b ha hb
  have he := Nat.card_congr (fixedByConjugateEquiv (X := X) (a : G) g)
  rw [hg] at he
  exact he.symm

theorem exists_moved_coset_of_ne_one {G : Type*} [Group G] [IsSimpleGroup G]
    (H : Subgroup G) (hH : H ≠ ⊤) (g : G) (hg : g ≠ 1) :
    ∃ x : G ⧸ H, g • x ≠ x := by
  have hcore : H.normalCore = ⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact False.elim (hH (top_unique (ht ▸ H.normalCore_le)))
  have hker : (MulAction.toPermHom G (G ⧸ H)).ker = ⊥ := by
    rw [← H.normalCore_eq_ker,hcore]
  by_contra hm
  have hgker : g ∈ (MulAction.toPermHom G (G ⧸ H)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply Equiv.Perm.ext
    intro x
    change g • x = x
    by_contra hx
    exact hm ⟨x,hx⟩
  rw [hker] at hgker
  exact hg hgker

theorem card_le_index_of_nonidentity_conjugate {G : Type*} [Group G]
    [Finite G] [IsSimpleGroup G] (E : Subgroup G) [Nontrivial E]
    (hconj : ∀ a b : E, a ≠ 1 → b ≠ 1 →
      ∃ g : G, g*(a : G)*g⁻¹=(b : G)) (H : Subgroup G) (hH : H ≠ ⊤) :
    Nat.card E ≤ H.index := by
  change Nat.card E ≤ Nat.card (G ⧸ H)
  apply card_le_of_nonidentity_conjugate E hconj
  obtain ⟨a,ha⟩ := exists_ne (1 : E)
  have ha' : (a : G) ≠ 1 := fun he => ha (Subtype.ext he)
  obtain ⟨x,hx⟩ := exists_moved_coset_of_ne_one H hH (a : G) ha'
  exact ⟨a,x,hx⟩

end SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
