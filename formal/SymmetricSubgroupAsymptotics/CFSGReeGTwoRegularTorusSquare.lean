import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedTorusRegularity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! A regular square parameter for the fixed Ree torus exists in every
simple-family field. A generator has order q-1 greater than four, so
its square is neither 1 nor -1. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoRegularTorusSquare
open CFSGReeGTwoFieldParameters

theorem exists_regular_square (m : ℕ) (hm : 1≤m) :
    ∃ t : (Field m)ˣ, t^2≠1 ∧ t^2≠-1 := by
  obtain ⟨t,ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (Field m)ˣ)
  have hq : 27≤3^(2*m+1) :=
    Nat.pow_le_pow_right (by decide : 1≤3) (by omega : 3≤2*m+1)
  have hc : 4<Nat.card ((Field m)ˣ) := by
    rw [Nat.card_units,field_card]
    omega
  have hfour : t^4≠1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    have hl := Nat.le_of_dvd (by decide : 0<4) hd
    rw [ht] at hl
    omega
  refine ⟨t,?_,?_⟩
  · intro he
    apply hfour
    calc
      t^4=(t^2)^2 := by rw [←pow_mul]
      _=1 := by rw [he,one_pow]
  · intro he
    apply hfour
    calc
      t^4=(t^2)^2 := by rw [←pow_mul]
      _=1 := by rw [he]; simp

end SymmetricSubgroupAsymptotics.CFSGReeGTwoRegularTorusSquare
