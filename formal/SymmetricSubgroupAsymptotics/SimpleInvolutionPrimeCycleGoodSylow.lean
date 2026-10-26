import SymmetricSubgroupAsymptotics.PrimeCycleSylowNormalizerSolvable
import SymmetricSubgroupAsymptotics.SimpleTwoGeneratorConjugateNormalClosure
import SymmetricSubgroupAsymptotics.CFSGGoodSylowOfTwoPSubgroups

/-! An involutory generating pair whose product acts as one prime cycle
gives a good Sylow prime when that prime occurs only once in the group
order. All conjugators and subgroups remain in the actual source group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeCycleGoodSylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem sylow_card_of_member_order (P : Sylow p G) (z : G) (hz : z ∈ P)
    (horder : orderOf z = p) (hnot : ¬p^2 ∣ Nat.card G) : Nat.card P = p := by
  obtain ⟨a,ha⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hd : p^a ∣ Nat.card G := by
    rw [←ha]
    exact (P : Subgroup G).card_subgroup_dvd_card
  have ha1 : a ≤ 1 := by
    by_contra h
    exact hnot ((Nat.pow_dvd_pow p (by omega : 2 ≤ a)).trans hd)
  have hpP : p ∣ Nat.card P := by
    let w : P := ⟨z,hz⟩
    have ho : orderOf w = p := (Subgroup.orderOf_coe w).symm.trans horder
    simpa only [ho] using orderOf_dvd_natCard w
  have ha0 : a ≠ 0 := by
    intro he
    rw [ha,he,pow_zero] at hpP
    have := (Nat.le_of_dvd (by decide : 0 < 1) hpP)
    have := (Fact.out : Nat.Prime p).two_le
    omega
  have he : a = 1 := by omega
  simpa only [he,pow_one] using ha

omit [Finite G] in
theorem closure_involution_product (x y : G)
    (hgen : Subgroup.closure ({x,y} : Set G) = ⊤) :
    Subgroup.closure ({x,x*y} : Set G) = ⊤ := by
  let R := Subgroup.closure ({x,x*y} : Set G)
  have hx : x ∈ R := Subgroup.subset_closure (Or.inl rfl)
  have hxy : x*y ∈ R := Subgroup.subset_closure (Or.inr rfl)
  have hy : y ∈ R := by
    simpa only [inv_mul_cancel_left] using R.mul_mem (R.inv_mem hx) hxy
  apply top_unique
  rw [←hgen]
  apply (Subgroup.closure_le R).mpr
  rintro z (rfl|rfl)
  · exact hx
  · exact hy

theorem goodSylowPrime [IsSimpleGroup G] {n : ℕ}
    [MulAction G (Fin n)] [FaithfulSMul G (Fin n)]
    (x y : G) (hx : x^2=1)
    (hgen : Subgroup.closure ({x,y} : Set G) = ⊤)
    (hn : n=p ∨ n=p+1) (hnot : ¬p^2 ∣ Nat.card G)
    (htype : (MulAction.toPermHom G (Fin n) (x*y)).cycleType = {p}) :
    CFSGReduction.GoodSylowPrime G p := by
  let a := x*y
  let rho := MulAction.toPermHom G (Fin n)
  have hrho : orderOf (rho a) = p := by
    change orderOf (MulAction.toPermHom G (Fin n) (x*y)) = p
    rw [←Equiv.Perm.lcm_cycleType,htype]
    simp
  have horder : orderOf a = p :=
    (orderOf_injective rho MulAction.toPerm_injective a).symm.trans hrho
  have hne : a ≠ 1 := by
    intro h
    rw [h,orderOf_one] at horder
    have := (Fact.out : Nat.Prime p).two_le
    omega
  have hU : IsPGroup p (Subgroup.zpowers a) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,horder,pow_one]
  have hV : IsPGroup p (Subgroup.zpowers (x*a*x⁻¹)) := by
    have hh := hU.map (MulAut.conj x).toMonoidHom
    rw [MonoidHom.map_zpowers] at hh
    exact hh
  have hgenerate : Subgroup.zpowers a ⊔ Subgroup.zpowers (x*a*x⁻¹) = ⊤ :=
    SimpleTwoGeneratorConjugateNormalClosure.zpowers_sup_eq_top x a hx hne
      (closure_involution_product x y hgen)
  obtain ⟨P,hP⟩ := hU.exists_le_sylow
  have haP : a ∈ P := hP (Subgroup.mem_zpowers a)
  have hsol : IsSolvable (Subgroup.normalizer (P : Set G)) :=
    PrimeCycleSylowNormalizerSolvable.sylow_normalizer_isSolvable P
      (sylow_card_of_member_order P a haP horder hnot) a haP hn htype
  exact CFSGReduction.goodSylowPrime_of_two_p_subgroups_and_exists_soluble_normalizer
    (Subgroup.zpowers a) (Subgroup.zpowers (x*a*x⁻¹)) hU hV hgenerate ⟨P,hsol⟩

end SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeCycleGoodSylow
