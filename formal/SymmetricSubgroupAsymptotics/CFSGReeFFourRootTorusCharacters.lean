import SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusExponents
import SymmetricSubgroupAsymptotics.CFSGReeFFourFieldParameters
import Mathlib.FieldTheory.Finite.Basic

/-! Actual characters of the two-unit parameter group for the fixed
ReeF4 torus. Every ambient E6 root character is nontrivial when m>0.
This arithmetic statement still awaits its separate all-height action
binding; m=0 is deliberately excluded from nontriviality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusCharacters
open CFSGNormTwoRootPairing CFSGReeFFourFieldParameters CFSGReeFFourRootTorusExponents

def rootCharacter (m : ℕ) (k : Roots CartanMatrix.E₆) :
    ((Field m)ˣ×(Field m)ˣ)→*(Field m)ˣ where
  toFun t := t.1^firstExponent m k.val*t.2^secondExponent m k.val
  map_one' := by simp only [Prod.fst_one,Prod.snd_one,one_zpow,mul_one]
  map_mul' a b := by
    simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
    ac_rfl

private theorem unit_card_cast (m : ℕ) :
    (Nat.card (Field m)ˣ : ℤ)=(2 : ℤ)^(2*m+1)-1 := by
  rw [Nat.card_units,field_card,Nat.cast_sub (Nat.one_le_pow _ _ (by decide : 1≤(2 : ℕ)))]
  norm_cast

theorem rootCharacter_nontrivial (m : ℕ) (hm : 0<m) (k : Roots CartanMatrix.E₆) :
    ∃t : (Field m)ˣ×(Field m)ˣ,rootCharacter m k t≠1 := by
  obtain ⟨g,hg⟩ := IsCyclic.exists_generator (α := (Field m)ˣ)
  have horder : (orderOf g : ℤ)=(2 : ℤ)^(2*m+1)-1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg,unit_card_cast]
  rcases root_exponent_nondivisible m hm k with ha|hb
  · refine ⟨(g,1),?_⟩
    intro he
    have hp : g^firstExponent m k.val=1 := by
      simpa only [rootCharacter,MonoidHom.coe_mk,OneHom.coe_mk,one_zpow,mul_one] using he
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hp
    rw [horder] at hd
    exact ha hd
  · refine ⟨(1,g),?_⟩
    intro he
    have hp : g^secondExponent m k.val=1 := by
      simpa only [rootCharacter,MonoidHom.coe_mk,OneHom.coe_mk,one_zpow,one_mul] using he
    have hd := orderOf_dvd_iff_zpow_eq_one.mpr hp
    rw [horder] at hd
    exact hb hd

theorem torus_parameter_card_odd (m : ℕ) : Odd (Nat.card ((Field m)ˣ×(Field m)ˣ)) := by
  rw [Nat.card_prod,Nat.card_units,field_card]
  have hq : 1≤2^(2*m+1) := Nat.one_le_pow _ _ (by decide : 1≤(2 : ℕ))
  have hmod : (2^(2*m+1) : ℕ)%2=0 := by
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : 2*m+1≠0))
  have hodd : Odd (2^(2*m+1)-1) := Nat.odd_iff.mpr (by omega)
  exact hodd.mul hodd

end SymmetricSubgroupAsymptotics.CFSGReeFFourRootTorusCharacters
