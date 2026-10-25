import SymmetricSubgroupAsymptotics.External.CFSG.Models.Mathieu22
import Mathlib.GroupTheory.OrderOfElement

/-! A literal order-four element in the pinned Mathieu22 permutation
construction. Pairwise disjoint cycle supports prove the eighth-power
identity; only one selected original coordinate proves fourth-power
nontriviality. No group order, identification, or catalogue is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOrderFour
open CFSG.Models.Mathieu22Construction

private theorem cycle_commute (l m : List (Fin 22))
    (hl : l.Nodup) (hm : m.Nodup) (hllen : 2 ≤ l.length) (hmlen : 2 ≤ m.length)
    (hd : l.Disjoint m) : Commute (List.formPerm l) (List.formPerm m) :=
  ((List.formPerm_disjoint_iff hl hm hllen hmlen).mpr hd).commute

private theorem cycle_eighth (l : List (Fin 22)) (hl : l.Nodup)
    (hlen : l.length ∣ 8) : (List.formPerm l)^8 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp
    ((orderOf_dvd_of_pow_eq_one (List.formPerm_pow_length_eq_one_of_nodup l hl)).trans hlen)

theorem b_eighth : b^8 = 1 := by
  let l₀ : List (Fin 22) := [0,17,10,19,18,8,3,1]
  let l₁ : List (Fin 22) := [2,14]
  let l₂ : List (Fin 22) := [4,7,6,15]
  let l₃ : List (Fin 22) := [5,21,12,13,9,11,16,20]
  have h01 := cycle_commute l₀ l₁ (by decide) (by decide) (by decide) (by decide)
    (by simp [List.Disjoint,l₀,l₁])
  have h02 := cycle_commute l₀ l₂ (by decide) (by decide) (by decide) (by decide)
    (by simp [List.Disjoint,l₀,l₂])
  have h03 := cycle_commute l₀ l₃ (by decide) (by decide) (by decide) (by decide)
    (by simp [List.Disjoint,l₀,l₃])
  have h12 := cycle_commute l₁ l₂ (by decide) (by decide) (by decide) (by decide)
    (by simp [List.Disjoint,l₁,l₂])
  have h13 := cycle_commute l₁ l₃ (by decide) (by decide) (by decide) (by decide)
    (by simp [List.Disjoint,l₁,l₃])
  have h23 := cycle_commute l₂ l₃ (by decide) (by decide) (by decide) (by decide)
    (by simp [List.Disjoint,l₂,l₃])
  have h0 := cycle_eighth l₀ (by decide) (by decide)
  have h1 := cycle_eighth l₁ (by decide) (by decide)
  have h2 := cycle_eighth l₂ (by decide) (by decide)
  have h3 := cycle_eighth l₃ (by decide) (by decide)
  change (((List.formPerm l₀*List.formPerm l₁)*List.formPerm l₂)*List.formPerm l₃)^8 = 1
  calc
    _ = (List.formPerm l₀)^8*(List.formPerm l₁)^8*
        (List.formPerm l₂)^8*(List.formPerm l₃)^8 := by
      rw [((h03.mul_left h13).mul_left h23).mul_pow,(h02.mul_left h12).mul_pow,h01.mul_pow]
    _ = 1 := by simp only [h0,h1,h2,h3,one_mul]

private theorem b_apply_first (x : Fin 22)
    (h1 : x ∉ ([2,14] : List (Fin 22)))
    (h2 : x ∉ ([4,7,6,15] : List (Fin 22)))
    (h3 : x ∉ ([5,21,12,13,9,11,16,20] : List (Fin 22))) :
    b x = List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) x := by
  simp only [b,Equiv.Perm.mul_apply,List.formPerm_apply_of_notMem h3,
    List.formPerm_apply_of_notMem h2,List.formPerm_apply_of_notMem h1]

theorem b_fourth_ne : b^4 ≠ 1 := by
  let l : List (Fin 22) := [0,17,10,19,18,8,3,1]
  have h0 : b 0 = 17 := by
    apply (b_apply_first 0 (by decide) (by decide) (by decide)).trans
    exact List.formPerm_apply_lt_getElem l (by decide) 0 (by decide)
  have h17 : b 17 = 10 := by
    apply (b_apply_first 17 (by decide) (by decide) (by decide)).trans
    exact List.formPerm_apply_lt_getElem l (by decide) 1 (by decide)
  have h10 : b 10 = 19 := by
    apply (b_apply_first 10 (by decide) (by decide) (by decide)).trans
    exact List.formPerm_apply_lt_getElem l (by decide) 2 (by decide)
  have h19 : b 19 = 18 := by
    apply (b_apply_first 19 (by decide) (by decide) (by decide)).trans
    exact List.formPerm_apply_lt_getElem l (by decide) 3 (by decide)
  have he18 : (b^4) (0 : Fin 22) = 18 := by
    simp only [pow_succ,Equiv.Perm.mul_apply,pow_zero,Equiv.Perm.one_apply,h0,h17,h10,h19]
  intro h
  have he : (b^4) (0 : Fin 22) = 0 := congrArg (fun g : Equiv.Perm (Fin 22) => g 0) h
  exact (by decide : (18 : Fin 22) ≠ 0) (he18.symm.trans he)

private def B : CFSG.Models.Mathieu22 :=
  ⟨b,Subgroup.subset_closure (Or.inr rfl)⟩

theorem exists_order_four : ∃ g : CFSG.Models.Mathieu22, orderOf g = 4 := by
  have hB8 : B^8 = 1 := Subtype.ext b_eighth
  have hB4 : B^4 ≠ 1 := by
    intro h
    have hv := congrArg (fun g : CFSG.Models.Mathieu22 => g.val) h
    change B.val^4 = 1 at hv
    rw [show B.val = b from rfl] at hv
    exact b_fourth_ne hv
  have hg4 : (B^2)^4 = 1 := by simpa only [←pow_mul] using hB8
  have hg2 : (B^2)^2 ≠ 1 := by simpa only [←pow_mul] using hB4
  refine ⟨B^2,?_⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hg2) (by simpa using hg4)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOrderFour
