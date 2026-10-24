import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldParameters

/-! The nontrivial unit needed by the derived regular witness exists
for m>0. No such choice is asserted for m=0. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourNontrivialTorusUnit
open CFSGReeFFourFieldParameters

theorem exists_torus_unit_ne_one (m : ℕ) (hm : 0<m) :
    ∃a : (Field m)ˣ,a≠1 := by
  have hq : 8≤Nat.card (Field m) := by
    rw [field_card]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega : 3≤2*m+1)
  have hc : 1<Nat.card ((Field m)ˣ) := by
    rw [Nat.card_units]
    omega
  by_contra hn
  have he : Nat.card ((Field m)ˣ)=1 := Nat.card_eq_one_iff_exists.mpr
    ⟨1,fun a=>by
      by_contra ha
      exact hn ⟨a,ha⟩⟩
  omega

end SymmetricSubgroupAsymptotics.CFSGReeFFourNontrivialTorusUnit
