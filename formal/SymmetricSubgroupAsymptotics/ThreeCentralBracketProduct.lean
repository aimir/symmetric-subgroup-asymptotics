import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.FinCases

/-! Three central diagonal commutators collect across four by three
ordered factors. Neither of the two input families is assumed abelian. -/
set_option autoImplicit false
set_option Elab.async false
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.ThreeCentralBracketProduct
variable {G : Type*} [Group G]

private theorem left_collect (a b c : G) (h : Commute a ⁅b,c⁆) :
    ⁅a*b,c⁆ = ⁅b,c⁆*⁅a,c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, h.eq]
  group

private theorem right_collect (a b c : G) (h : Commute b ⁅a,c⁆) :
    ⁅a,b*c⁆ = ⁅a,b⁆*⁅a,c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅a,b⁆*b*⁅a,c⁆*b⁻¹ = ⁅a,b⁆*(b*⁅a,c⁆)*b⁻¹ := by group
    _ = ⁅a,b⁆*(⁅a,c⁆*b)*b⁻¹ := by rw [h.eq]
    _ = _ := by group

theorem collect (a : Fin 4 → G) (b c : Fin 3 → G)
    (hbracket : ∀ i j, ⁅a i,b j⁆ = if i = j.castSucc then c j else 1)
    (hac : ∀ i j, Commute (a i) (c j))
    (hbc : ∀ i j, Commute (b i) (c j))
    (hcc : ∀ i j, Commute (c i) (c j)) :
    ⁅a 0*a 1*a 2*a 3,b 0*b 1*b 2⁆ = c 0*c 1*c 2 := by
  have entry (i : Fin 4) (j k : Fin 3) : Commute (b k) ⁅a i,b j⁆ := by
    rw [hbracket i j]
    split_ifs
    · exact hbc k j
    · exact Commute.one_right _
  have row (i : Fin 4) :
      ⁅a i,b 0*b 1*b 2⁆ = ⁅a i,b 0⁆*⁅a i,b 1⁆*⁅a i,b 2⁆ := by
    rw [right_collect _ _ _ ((entry i 2 0).mul_left (entry i 2 1)),
      right_collect _ _ _ (entry i 1 0)]
  have h0 : ⁅a 0,b 0*b 1*b 2⁆ = c 0 := by rw [row,hbracket,hbracket,hbracket]; simp
  have h1 : ⁅a 1,b 0*b 1*b 2⁆ = c 1 := by rw [row,hbracket,hbracket,hbracket]; simp
  have h2 : ⁅a 2,b 0*b 1*b 2⁆ = c 2 := by rw [row,hbracket,hbracket,hbracket]; simp
  have h3 : ⁅a 3,b 0*b 1*b 2⁆ = 1 := by rw [row,hbracket,hbracket,hbracket]; simp
  have h01 : ⁅a 0*a 1,b 0*b 1*b 2⁆ = c 1*c 0 := by
    rw [left_collect _ _ _ (by rw [h1]; exact hac 0 1),h1,h0]
  have h012 : ⁅a 0*a 1*a 2,b 0*b 1*b 2⁆ = c 2*(c 1*c 0) := by
    rw [left_collect _ _ _ (by rw [h2]; exact (hac 0 2).mul_left (hac 1 2)),h2,h01]
  calc
    _ = c 2*(c 1*c 0) := by
      rw [left_collect _ _ _ (by rw [h3]; exact Commute.one_right _),h3,one_mul,h012]
    _ = c 2*(c 0*c 1) := by rw [(hcc 1 0).eq]
    _ = (c 0*c 1)*c 2 := ((hcc 2 0).mul_right (hcc 2 1)).eq

end SymmetricSubgroupAsymptotics.ThreeCentralBracketProduct
