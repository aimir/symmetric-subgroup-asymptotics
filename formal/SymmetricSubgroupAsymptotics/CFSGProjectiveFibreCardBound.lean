import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Field.Defs

/-! A map whose fibres consist of proportional nonzero vectors has
at most q elements per fibre. This coarse bound avoids choosing a
projective normalization or assuming a projective counting formula. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFibreCardBound
variable {K V C Y : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem fibre_card_le [Finite K] (v : C → V) (hv : Function.Injective v) (f : C → Y)
    (hs : ∀ c d, f c = f d → ∃ a : K, v c = a • v d) (y : Y) :
    Nat.card {c : C // f c = y} ≤ Nat.card K := by
  classical
  by_cases hn : Nonempty {c : C // f c = y}
  · let d := Classical.choice hn
    have hex (c : {c : C // f c = y}) : ∃ a : K, v c.val = a • v d.val :=
      hs c.val d.val (c.property.trans d.property.symm)
    let a : {c : C // f c = y} → K := fun c => Classical.choose (hex c)
    have ha (c : {c : C // f c = y}) : v c.val = a c • v d.val :=
      Classical.choose_spec (hex c)
    have hi : Function.Injective a := by
      intro c c' he
      apply Subtype.ext
      apply hv
      rw [ha c, ha c', he]
    exact Nat.card_le_card_of_injective a hi
  · have hz : IsEmpty {c : C // f c = y} := not_nonempty_iff.mp hn
    have hc : Nat.card {c : C // f c = y} = 0 := Nat.card_eq_zero.mpr (Or.inl hz)
    rw [hc]
    exact Nat.zero_le _

theorem card_le_mul [Finite K] [Finite C] [Finite Y]
    (v : C → V) (hv : Function.Injective v) (f : C → Y)
    (hs : ∀ c d, f c = f d → ∃ a : K, v c = a • v d) :
    Nat.card C ≤ Nat.card Y * Nat.card K := by
  classical
  letI : Fintype Y := Fintype.ofFinite Y
  calc
    Nat.card C = Nat.card (Σ y : Y, {c : C // f c = y}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv f)).symm
    _ = ∑ y : Y, Nat.card {c : C // f c = y} := Nat.card_sigma
    _ ≤ ∑ _y : Y, Nat.card K := Finset.sum_le_sum (fun y _ => fibre_card_le v hv f hs y)
    _ = Nat.card Y * Nat.card K := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, Nat.card_eq_fintype_card]

end SymmetricSubgroupAsymptotics.CFSGProjectiveFibreCardBound
