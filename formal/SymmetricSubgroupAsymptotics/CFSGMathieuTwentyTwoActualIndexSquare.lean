import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedWordOrder
import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoOrderFour
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport
import Mathlib.GroupTheory.Sylow

/-! The actual pinned22-point generated subgroup has strict least-index
square under inherited simplicity. Literal orders5,8 and the existing
selected period11 give440 divisibility; Sylow11 excludes order440. No
known sporadic order, identification, action catalogue or enumeration is
assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoActualIndexSquare
open PrimitiveSocleRawStructure CFSG.Models.Mathieu22Construction
open CFSGMathieuTwentyTwoSelectedWordOrder

private theorem a_first (x : Fin 22)
    (h1 : x ∉ ([1,14,21,10,18] : List (Fin 22)))
    (h2 : x ∉ ([2,7,8,16,12] : List (Fin 22)))
    (h3 : x ∉ ([3,13,9,19,20] : List (Fin 22))) :
    a x=List.formPerm ([0,11,4,5,15] : List (Fin 22)) x := by
  simp only [a,Equiv.Perm.mul_apply,List.formPerm_apply_of_notMem h3,
    List.formPerm_apply_of_notMem h2,List.formPerm_apply_of_notMem h1]

private theorem a_period_five : (a^5) (0 : Fin 22)=0 := by
  let l : List (Fin 22) := [0,11,4,5,15]
  have h0 : a (0 : Fin 22)=11 := by
    apply (a_first 0 (by decide) (by decide) (by decide)).trans
    exact List.formPerm_apply_lt_getElem l (by decide) 0 (by decide)
  have h11 : a (11 : Fin 22)=4 := by
    apply (a_first 11 (by decide) (by decide) (by decide)).trans
    exact List.formPerm_apply_lt_getElem l (by decide) 1 (by decide)
  have h4 : a (4 : Fin 22)=5 := by
    apply (a_first 4 (by decide) (by decide) (by decide)).trans
    exact List.formPerm_apply_lt_getElem l (by decide) 2 (by decide)
  have h5 : a (5 : Fin 22)=15 := by
    apply (a_first 5 (by decide) (by decide) (by decide)).trans
    exact List.formPerm_apply_lt_getElem l (by decide) 3 (by decide)
  have h15 : a (15 : Fin 22)=0 := by
    apply (a_first 15 (by decide) (by decide) (by decide)).trans
    simpa [l] using List.formPerm_apply_getElem l (by decide) 4 (by decide)
  simp only [pow_succ,pow_zero,Equiv.Perm.mul_apply,Equiv.Perm.one_apply,h0,h11,h4,h5,h15]

theorem five_dvd_order : 5 ∣ Nat.card CFSG.Models.Mathieu22 := by
  let A : CFSG.Models.Mathieu22 := ⟨a,Subgroup.subset_closure (Or.inl rfl)⟩
  apply PrimePeriodSimpleQuotientIndex.prime_dvd_card_of_point_period
    5 (by decide) A (0 : Fin 22)
  · exact a_period_five
  · have h0 : a (0 : Fin 22)=11 := by
      apply (a_first 0 (by decide) (by decide) (by decide)).trans
      exact List.formPerm_apply_lt_getElem
        ([0,11,4,5,15] : List (Fin 22)) (by decide) 0 (by decide)
    change a (0 : Fin 22)≠0
    rw [h0]
    decide

private theorem eight_dvd_of_powers {G : Type} [Group G] (x : G)
    (h4 : x^4≠1) (h8 : x^8=1) : 8 ∣ Nat.card G := by
  have ho : orderOf x=8 :=
    orderOf_eq_prime_pow (p:=2) (n:=2) (by simpa using h4) (by simpa using h8)
  rw [←ho]
  exact orderOf_dvd_natCard x

theorem eight_dvd_order : 8 ∣ Nat.card CFSG.Models.Mathieu22 := by
  let B : CFSG.Models.Mathieu22 := ⟨b,Subgroup.subset_closure (Or.inr rfl)⟩
  have hB8 : B^8=1 := Subtype.ext CFSGMathieuTwentyTwoOrderFour.b_eighth
  have hB4 : B^4≠1 := by
    intro h
    have hv := congrArg (fun g : CFSG.Models.Mathieu22 => g.val) h
    change B.val^4=1 at hv
    rw [show B.val=b from rfl] at hv
    exact CFSGMathieuTwentyTwoOrderFour.b_fourth_ne hv
  exact eight_dvd_of_powers B hB4 hB8

theorem four_forty_dvd_order : 440 ∣ Nat.card CFSG.Models.Mathieu22 := by
  have h40 : 40 ∣ Nat.card CFSG.Models.Mathieu22 :=
    (show Nat.Coprime 5 8 by decide).mul_dvd_of_dvd_of_dvd five_dvd_order eight_dvd_order
  exact (show Nat.Coprime 40 11 by decide).mul_dvd_of_dvd_of_dvd
    h40 eleven_dvd_order

private theorem divisor_forty_mod_eleven (m : ℕ) (hd : m∣40) (hm : m%11=1) : m=1 := by
  have hle : m≤40 := Nat.le_of_dvd (by decide) hd
  interval_cases m <;> norm_num at *

private theorem not_simple_order_four_forty {G : Type} [Group G] [Finite G]
    [IsSimpleGroup G] (hcard : Nat.card G=440) : False := by
  letI : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨P⟩ := Sylow.nonempty (p:=11) (G:=G)
  have hPcard : Nat.card P=11 := by
    rw [P.card_eq_multiplicity,hcard]
    decide +kernel
  have hindex : P.index=40 := by
    have hh := (P : Subgroup G).card_mul_index
    rw [hPcard,hcard] at hh
    omega
  have hd : Nat.card (Sylow 11 G) ∣ 40 := by simpa only [hindex] using P.card_dvd_index
  have hm := card_sylow_modEq_one 11 G
  have hc : Nat.card (Sylow 11 G)=1 := by
    change Nat.card (Sylow 11 G)%11=1%11 at hm
    exact divisor_forty_mod_eleven _ hd hm
  letI : Subsingleton (Sylow 11 G) := Finite.card_le_one_iff_subsingleton.mp hc.le
  letI : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) inferInstance with h|h
  · have hh : Nat.card P=1 := by rw [h,Subgroup.card_bot]
    omega
  · have hh : Nat.card P=Nat.card G := by rw [h,Subgroup.card_top]
    omega

theorem order_gt_four_eighty_four [IsSimpleGroup CFSG.Models.Mathieu22] :
    484 < Nat.card CFSG.Models.Mathieu22 := by
  by_contra h
  have hp : 0 < Nat.card CFSG.Models.Mathieu22 := Nat.card_pos
  obtain ⟨k,hk⟩ := four_forty_dvd_order
  have hc : Nat.card CFSG.Models.Mathieu22=440 := by omega
  exact not_simple_order_four_forty hc

theorem least_index_le_twenty_two (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Mathieu22 ell) : ell ≤ 22 := by
  let K := MulAction.stabilizer CFSG.Models.Mathieu22 (0 : Fin 22)
  have hK : K≠⊤ := by
    intro h
    have hg : selectedModelWord∈K := by rw [h]; trivial
    have he : selectedModelWord • (0 : Fin 22)=0 := hg
    change ((selectedModelWord : Equiv.Perm (Fin 22)) (0 : Fin 22))=0 at he
    rw [selectedWord_coe] at he
    exact CFSGMathieuTwentyTwoSelectedTraceTransitions.moved_zero he
  have hi : K.index ≤ 22 := by
    simpa only [Nat.card_fin] using
      (MulAction.index_stabilizer CFSG.Models.Mathieu22 (0 : Fin 22)).trans_le
        (Set.ncard_le_card _)
  exact (hell.2 K hK).trans hi

theorem index_square [IsSimpleGroup CFSG.Models.Mathieu22] (ell : ℕ)
    (hell : LeastProperIndex CFSG.Models.Mathieu22 ell) :
    ell^2 < Nat.card CFSG.Models.Mathieu22 := by
  have hi := least_index_le_twenty_two ell hell
  have ho := order_gt_four_eighty_four
  exact (Nat.pow_le_pow_left hi 2).trans_lt ho

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoActualIndexSquare
