import SymmetricSubgroupAsymptotics.CFSGCoTwoLiteralRepresentation

/-! Positive forms of the SAME old Co2 relators, under just x²=y⁵=1.
This algebraic bridge contains no finite data, recognition or order claim. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGCoTwoPositiveRelatorWords
open CFSG.Models CFSGCoTwoLiteralRepresentation

def r3 {G : Type} [Group G] (a b : G) := a * b^2
def r4 {G : Type} [Group G] (a b : G) := a * b^4 * a * b
def r5 {G : Type} [Group G] (a b : G) := a * b^3 * a * b^2
def r6 {G : Type} [Group G] (a b : G) := a * b^4 * a * b^4 * a * b * a * b
def r7 {G : Type} [Group G] (a b : G) :=
  a * b^4 * a * b^3 * a * b^4 * a * b * a * b^2 * a * b
def r8 {G : Type} [Group G] (a b : G) := a * b^2 * a * b^4 * a * b * a * b^3
def r9 {G : Type} [Group G] (a b : G) :=
  a * b^2 * a * b^4 * a * b^2 * a * b^3 * a * b * a * b^3
def r10 {G : Type} [Group G] (a b : G) := a * b * a * b^2 * a * b^4 * a * b^3

private theorem inverse_data {G : Type} [Group G] (a b : G)
    (ha : a^2=1) (hb : b^5=1) :
    a⁻¹=a ∧ b⁻¹=b^4 ∧ (b⁻¹)^2=b^3 := by
  have hai : a⁻¹=a := by
    have hl : a⁻¹*a=1 := by group
    have hr : a*a=1 := by simpa only [pow_two] using ha
    exact mul_right_cancel (hl.trans hr.symm)
  have hbi : b⁻¹=b^4 := by
    have hl : b⁻¹*b=1 := by group
    have hr : b^4*b=1 := by rw [←pow_succ]; exact hb
    exact mul_right_cancel (hl.trans hr.symm)
  have hbi2 : (b⁻¹)^2=b^3 := by
    have hl : (b⁻¹)^2*b^2=1 := by group
    have hr : b^3*b^2=1 := by rw [←pow_add]; exact hb
    exact mul_right_cancel (hl.trans hr.symm)
  exact ⟨hai,hbi,hbi2⟩

theorem comm_b_eq {G : Type} [Group G] (a b : G) (ha : a^2=1) (hb : b^5=1) :
    commWord a b=r4 a b := by
  obtain ⟨hai,hbi,-⟩ := inverse_data a b ha hb
  simp only [commWord,r4,hai,hbi]

theorem comm_b2_eq {G : Type} [Group G] (a b : G) (ha : a^2=1) (hb : b^5=1) :
    commWord a (b^2)=r5 a b := by
  obtain ⟨hai,-,hbi2⟩ := inverse_data a b ha hb
  simp only [commWord,←inv_pow,r5,hai,hbi2]

theorem comm_bab_eq {G : Type} [Group G] (a b : G) (ha : a^2=1) (hb : b^5=1) :
    commWord a (b*a*b)=r6 a b := by
  obtain ⟨hai,hbi,-⟩ := inverse_data a b ha hb
  simp only [commWord,mul_inv_rev,r6]
  simp only [hai,hbi]
  group

theorem comm_long_eq {G : Type} [Group G] (a b : G) (ha : a^2=1) (hb : b^5=1) :
    commWord a (b*a*b^2*a*b)=r7 a b := by
  obtain ⟨hai,hbi,hbi2⟩ := inverse_data a b ha hb
  simp only [commWord,mul_inv_rev,←inv_pow,r7]
  simp only [hbi2]
  simp only [hai,hbi]
  group

theorem comm_negative_eq {G : Type} [Group G] (a b : G) (ha : a^2=1) (hb : b^5=1) :
    commWord a (b*a*(b⁻¹)^2)=r8 a b := by
  obtain ⟨hai,hbi,hbi2⟩ := inverse_data a b ha hb
  simp only [commWord,mul_inv_rev,←inv_pow,inv_inv,r8]
  simp only [hbi2]
  simp only [hai,hbi]
  group

theorem comm_double_negative_eq {G : Type} [Group G]
    (a b : G) (ha : a^2=1) (hb : b^5=1) :
    commWord a ((b⁻¹)^2*a*b*a*(b⁻¹)^2)=r9 a b := by
  obtain ⟨hai,hbi,hbi2⟩ := inverse_data a b ha hb
  simp only [commWord,mul_inv_rev,←inv_pow,inv_inv,r9]
  simp only [hbi2]
  simp only [hai,hbi]
  group

theorem last_eq {G : Type} [Group G] (a b : G) (ha : a^2=1) (hb : b^5=1) :
    a*b*a*b^2*a*b⁻¹*a*(b⁻¹)^2=r10 a b := by
  obtain ⟨-,hbi,hbi2⟩ := inverse_data a b ha hb
  simp only [hbi2]
  simp only [hbi,r10]

theorem packet_of_positive_powers {G : Type} [Group G] (a b : G)
    (ha : a^2=1) (hb : b^5=1)
    (h3 : (r3 a b)^9=1) (h4 : (r4 a b)^4=1)
    (h5 : (r5 a b)^4=1) (h6 : (r6 a b)^3=1)
    (h7 : (r7 a b)^2=1) (h8 : (r8 a b)^3=1)
    (h9 : (r9 a b)^2=1) (h10 : (r10 a b)^7=1) : RelatorPacket a b where
  first := ha
  second := hb
  third := h3
  fourth := by rw [comm_b_eq a b ha hb]; exact h4
  fifth := by rw [comm_b2_eq a b ha hb]; exact h5
  sixth := by rw [comm_bab_eq a b ha hb]; exact h6
  seventh := by rw [comm_long_eq a b ha hb]; exact h7
  eighth := by rw [comm_negative_eq a b ha hb]; exact h8
  ninth := by rw [comm_double_negative_eq a b ha hb]; exact h9
  tenth := by rw [last_eq a b ha hb]; exact h10

end SymmetricSubgroupAsymptotics.CFSGCoTwoPositiveRelatorWords
