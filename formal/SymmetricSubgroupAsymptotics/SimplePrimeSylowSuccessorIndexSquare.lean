import SymmetricSubgroupAsymptotics.SimpleInvolutionPrimeDegreeGoodSylow
import Mathlib.GroupTheory.Transfer

/-! Burnside transfer excludes a self-centralizing Sylow normalizer in a
nonabelian simple source. The resulting normalizer factor improves the
strict square from degree p to degree p+1, without a group-order port. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SimplePrimeSylowSuccessorIndexSquare
open PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    {p : ℕ} [Fact p.Prime]

theorem not_normalizer_le_centralizer (hn : ¬IsMulCommutative G)
    (P : Sylow p G) (hP : Nat.card P = p) :
    ¬Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
  intro hNC
  let f := MonoidHom.transferSylow P hNC
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hNC
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · have htop : (P : Subgroup G) = ⊤ := by
      have hh := hcompl.sup_eq_top
      change f.ker ⊔ (P : Subgroup G) = ⊤ at hh
      simpa only [hb,bot_sup_eq] using hh
    have hc : Nat.card G = p := by
      have he : Nat.card P = Nat.card G := by rw [htop,Subgroup.card_top]
      exact he.symm.trans hP
    letI : IsCyclic G := isCyclic_of_prime_card hc
    exact hn inferInstance
  · have hnd := MonoidHom.not_dvd_card_ker_transferSylow P hNC
    change ¬p ∣ Nat.card f.ker at hnd
    rw [ht,Subgroup.card_top] at hnd
    apply hnd
    have hd := (P : Subgroup G).card_subgroup_dvd_card
    simpa only [hP] using hd

theorem normalizer_card_ge_twice_prime (hn : ¬IsMulCommutative G)
    (P : Sylow p G) (hP : Nat.card P = p) :
    2*p ≤ Nat.card (Subgroup.normalizer (P : Set G)) := by
  let N := Subgroup.normalizer (P : Set G)
  letI : IsCyclic P := isCyclic_of_prime_card hP
  have hd : p ∣ Nat.card N := by
    have hh := Subgroup.card_dvd_of_le (P : Subgroup G).le_normalizer
    simpa only [hP] using hh
  obtain ⟨k,hk⟩ := hd
  have hkpos : 0 < k := by
    have hc : 0 < Nat.card N := Nat.card_pos
    by_contra h
    have he : k = 0 := by omega
    rw [he,mul_zero] at hk
    omega
  have hk2 : 2 ≤ k := by
    by_contra h
    have he : k = 1 := by omega
    have hc : Nat.card N = p := by simpa only [he,mul_one] using hk
    have hEq : (P : Subgroup G) = N :=
      Subgroup.eq_of_le_of_card_ge (P : Subgroup G).le_normalizer
        (by exact (Nat.le_of_eq hc).trans (Nat.le_of_eq hP.symm))
    apply not_normalizer_le_centralizer hn P hP
    exact hEq.symm.le.trans (P : Subgroup G).le_centralizer
  rw [hk]
  nlinarith

theorem sylow_count_ge_prime_succ (hn : ¬IsMulCommutative G)
    (P : Sylow p G) (hP : Nat.card P = p) : p+1 ≤ Nat.card (Sylow p G) := by
  have hp := (Fact.out : Nat.Prime p).two_le
  have hne : Nat.card (Sylow p G) ≠ 1 := by
    intro hc
    letI : Subsingleton (Sylow p G) := Finite.card_le_one_iff_subsingleton.mp hc.le
    letI : (P : Subgroup G).Normal := Sylow.normal_of_subsingleton P
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup G) inferInstance with hb | ht
    · have hh : Nat.card P = 1 := by rw [hb,Subgroup.card_bot]
      omega
    · have hh : Nat.card G = p := by
        have he : Nat.card P = Nat.card G := by rw [ht,Subgroup.card_top]
        exact he.symm.trans hP
      letI : IsCyclic G := isCyclic_of_prime_card hh
      exact hn inferInstance
  have hmod : Nat.card (Sylow p G) % p = 1 := by
    have hm := card_sylow_modEq_one p G
    change Nat.card (Sylow p G) % p = 1 % p at hm
    simpa only [Nat.mod_eq_of_lt (show 1 < p by omega)] using hm
  by_contra h
  have hle : Nat.card (Sylow p G) ≤ p := by omega
  by_cases he : Nat.card (Sylow p G) = p
  · rw [he,Nat.mod_self] at hmod
    omega
  · have hlt : Nat.card (Sylow p G) < p := by omega
    rw [Nat.mod_eq_of_lt hlt] at hmod
    exact hne hmod

theorem order_gt_prime_succ_square (hn : ¬IsMulCommutative G)
    (P : Sylow p G) (hP : Nat.card P = p) (hp3 : 3 ≤ p) :
    (p+1)^2 < Nat.card G := by
  have hN := normalizer_card_ge_twice_prime hn P hP
  have hcount := sylow_count_ge_prime_succ hn P hP
  have hprod : Nat.card (Subgroup.normalizer (P : Set G)) * Nat.card (Sylow p G) =
      Nat.card G := by
    have hh := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [←P.card_eq_index_normalizer] at hh
    exact hh
  have hb := Nat.mul_le_mul hN hcount
  rw [hprod] at hb
  nlinarith

theorem least_index_square_of_prime_cycle [MulAction G (Fin (p+1))]
    [FaithfulSMul G (Fin (p+1))]
    (hn : ¬IsMulCommutative G) (hp3 : 3 ≤ p) (g : G)
    (htype : (MulAction.toPermHom G (Fin (p+1)) g).cycleType = {p})
    (ell : ℕ) (hell : LeastProperIndex G ell) : ell^2 < Nat.card G := by
  let rho := MulAction.toPermHom G (Fin (p+1))
  have hperm : orderOf (rho g) = p := by
    change orderOf (MulAction.toPermHom G (Fin (p+1)) g) = p
    rw [←Equiv.Perm.lcm_cycleType,htype]
    simp
  have ho : orderOf g = p :=
    (orderOf_injective rho MulAction.toPerm_injective g).symm.trans hperm
  have hU : IsPGroup p (Subgroup.zpowers g) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,ho,pow_one]
  obtain ⟨P,hP⟩ := hU.exists_le_sylow
  have hgP : g ∈ P := hP (Subgroup.mem_zpowers g)
  have hcard : Nat.card P = p :=
    SimpleInvolutionPrimeCycleGoodSylow.sylow_card_of_member_order P g hgP ho
      (PrimeDegreeFactorialMultiplicity.source_card_prime_square_not_dvd (Or.inr rfl))
  have hex : ∃ i : Fin (p+1), rho g i ≠ i := by
    by_contra h
    have he : rho g = 1 := by
      apply Equiv.Perm.ext
      intro i
      exact not_not.mp (fun hi => h ⟨i,hi⟩)
    rw [he,orderOf_one] at hperm
    omega
  obtain ⟨i,hi⟩ := hex
  let K := MulAction.stabilizer G i
  have hK : K ≠ ⊤ := by
    intro h
    have hg : g ∈ K := by rw [h]; trivial
    exact hi hg
  have hidx : K.index ≤ p+1 := by
    simpa only [Nat.card_fin] using
      (MulAction.index_stabilizer G i).trans_le (Set.ncard_le_card _)
  exact (Nat.pow_le_pow_left ((hell.2 K hK).trans hidx) 2).trans_lt
    (order_gt_prime_succ_square hn P hcard hp3)

end SymmetricSubgroupAsymptotics.SimplePrimeSylowSuccessorIndexSquare
