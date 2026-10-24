import Mathlib.Data.Finite.Card
import Mathlib.Data.Fintype.Sum
import Lean.Elab.Tactic.Omega

/-! A homogeneous actual partition with at least two classes has every
class of size at most half the carrier. No primitivity is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.TransitiveKernelClassMultiplicity

variable {I C : Type} [Finite I] (key : I → C)
    (htransport : ∀ i j : I, ∃ e : I ≃ I, e i = j ∧
      ∀ x y, key (e x) = key (e y) ↔ key x = key y)

/-- Actual partition transport gives an equivalence of literal fibres. -/
def fibreEquiv (i j : I) : {x : I // key x = key i} ≃ {x : I // key x = key j} := by
  let e : I ≃ I := Classical.choose (htransport i j)
  have he := (Classical.choose_spec (htransport i j)).1
  have hkey := (Classical.choose_spec (htransport i j)).2
  refine {
    toFun := fun x => ⟨e x,?_⟩
    invFun := fun y => ⟨e.symm y,?_⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x)
    right_inv := fun y => Subtype.ext (e.apply_symm_apply y) }
  · rw [←he]
    exact (hkey x i).mpr x.property
  · apply (hkey (e.symm y) i).mp
    rw [e.apply_symm_apply,he]
    exact y.property

include htransport in
/-- Two disjoint equal-sized classes occupy twice one class's size. -/
theorem fibre_card_le_half (htwo : ∃ i j : I, key i ≠ key j) (i : I) :
    Nat.card {x : I // key x = key i} ≤ Nat.card I / 2 := by
  obtain ⟨a,b,hab⟩ := htwo
  obtain ⟨j,hij⟩ : ∃ j : I, key i ≠ key j := by
    by_cases ha : key i = key a
    · exact ⟨b,by intro h; exact hab (ha.symm.trans h)⟩
    · exact ⟨a,ha⟩
  let A := {x : I // key x = key i}
  let B := {x : I // key x = key j}
  let join : A ⊕ B → I := Sum.elim Subtype.val Subtype.val
  have hinj : Function.Injective join := by
    intro x y h
    cases x with
    | inl x =>
      cases y with
      | inl y => exact congrArg Sum.inl (Subtype.ext h)
      | inr y =>
        exact (hij (x.property.symm.trans ((congrArg key h).trans y.property))).elim
    | inr x =>
      cases y with
      | inl y =>
        exact (hij (y.property.symm.trans ((congrArg key h.symm).trans x.property))).elim
      | inr y => exact congrArg Sum.inr (Subtype.ext h)
  have hc := Nat.card_le_card_of_injective join hinj
  have he : Nat.card A = Nat.card B := Nat.card_congr (fibreEquiv key htransport i j)
  change Nat.card (A ⊕ B) ≤ Nat.card I at hc
  rw [Nat.card_sum,←he] at hc
  change Nat.card A ≤ Nat.card I / 2
  omega

include htransport in
/-- The bound is stated also for unrepresented labels, whose fibres are empty. -/
theorem all_fibres_card_le_half (htwo : ∃ i j : I, key i ≠ key j) (c : C) :
    Nat.card {x : I // key x = c} ≤ Nat.card I / 2 := by
  by_cases hc : ∃ i : I, key i = c
  · obtain ⟨i,rfl⟩ := hc
    exact fibre_card_le_half key htransport htwo i
  · have hempty : IsEmpty {x : I // key x = c} := ⟨fun x => hc ⟨x,x.property⟩⟩
    rw [(Finite.card_eq_zero_iff).mpr hempty]
    exact Nat.zero_le _

end SymmetricSubgroupAsymptotics.TransitiveKernelClassMultiplicity
