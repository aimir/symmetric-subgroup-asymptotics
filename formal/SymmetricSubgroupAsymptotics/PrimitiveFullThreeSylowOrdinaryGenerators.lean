import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.Sylow
import SymmetricSubgroupAsymptotics.NaturalDegreeFiveSocleOrdinaryGenerators

/-! Full ambient Sylow3 order supplies an actual conjugate of a3-cycle.
Jordan then identifies a primitive subgroup as A_n or S_n, giving two
generators without model recognition or a permutation-group catalogue. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.PrimitiveFullThreeSylowOrdinaryGenerators
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem exists_three_cycle_mem {n : ℕ} (hn : 3≤n)
    (J : Subgroup (Equiv.Perm (Fin n)))
    (hval : (Nat.card J).factorization 3=(Nat.card (Equiv.Perm (Fin n))).factorization 3) :
    ∃ c : Equiv.Perm (Fin n), c∈J ∧ c.IsThreeCycle := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let d : Fin n := ⟨2,by omega⟩
  let c := Equiv.swap a b*Equiv.swap a d
  have h3 : c.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same
    (by intro he; have hv := congrArg Fin.val he; change (0 : ℕ)=1 at hv; omega)
    (by intro he; have hv := congrArg Fin.val he; change (0 : ℕ)=2 at hv; omega)
    (by intro he; have hv := congrArg Fin.val he; change (1 : ℕ)=2 at hv; omega)
  have ho : orderOf c=3 := by
    rw [←Equiv.Perm.lcm_cycleType,h3.cycleType]
    simp
  have hC : IsPGroup 3 (Subgroup.zpowers c) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers,ho,pow_one]
  obtain ⟨Q,hQ⟩ := hC.exists_le_sylow
  have hcQ : c∈(Q : Subgroup (Equiv.Perm (Fin n))) := hQ (Subgroup.mem_zpowers c)
  let P : Sylow 3 J := Classical.choice inferInstance
  let H : Subgroup (Equiv.Perm (Fin n)) := (P : Subgroup J).map J.subtype
  have hH : Nat.card H=3^(Nat.card (Equiv.Perm (Fin n))).factorization 3 := by
    dsimp only [H]
    rw [Subgroup.card_map_of_injective J.subtype_injective,P.card_eq_multiplicity,hval]
  let R : Sylow 3 (Equiv.Perm (Fin n)) := Sylow.ofCard H hH
  have hHJ : H≤J := by
    rintro x ⟨j,hj,rfl⟩
    exact j.property
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin n)) Q R
  have hcR : g*c*g⁻¹∈(R : Subgroup (Equiv.Perm (Fin n))) := by
    rw [←hg]
    change (MulAut.conj g) c ∈ (MulAut.conj g) • (Q : Subgroup (Equiv.Perm (Fin n)))
    exact Subgroup.smul_mem_pointwise_smul c (MulAut.conj g) _ hcQ
  refine ⟨g*c*g⁻¹,hHJ hcR,?_⟩
  simpa only [Equiv.Perm.IsThreeCycle,Equiv.Perm.cycleType_conj] using h3

theorem genRank_le_two {n : ℕ} (hn : 5≤n)
    (J : Subgroup (Equiv.Perm (Fin n))) (hp : MulAction.IsPreprimitive J (Fin n))
    (hval : (Nat.card J).factorization 3=(Nat.card (Equiv.Perm (Fin n))).factorization 3) :
    MarkedC4.genRank J≤2 := by
  obtain ⟨c,hc,h3⟩ := exists_three_cycle_mem (by omega) J hval
  have hA : alternatingGroup (Fin n)≤J :=
    Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hp h3 hc
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa only [Nat.card_fin] using hn)
  rcases indexTwo_maximal (alternatingGroup (Fin n)) alternatingGroup.index_eq_two J hA with hAlt | hAll
  · rw [hAlt]
    exact CFSGAlternatingGeneration.genRank_le_two n hn
  · let e : J ≃* Equiv.Perm (Fin n) :=
      (MulEquiv.subgroupCongr hAll).trans Subgroup.topEquiv
    exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv e).le.trans
      (NaturalDegreeFiveSocleOrdinaryGenerators.symmetric_genRank_le_two n (by omega))

theorem genRank_le_two_of_eightyOne_dvd {n : ℕ} (hn : n=9 ∨ n=10)
    (J : Subgroup (Equiv.Perm (Fin n))) (hp : MulAction.IsPreprimitive J (Fin n))
    (h81 : 81 ∣ Nat.card J) : MarkedC4.genRank J≤2 := by
  have hf : (Nat.card (Equiv.Perm (Fin n))).factorization 3=4 := by
    rw [Nat.card_perm,Nat.card_fin]
    rcases hn with rfl | rfl <;> decide +kernel
  have hdiv := J.card_subgroup_dvd_card
  have hhi := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdiv 3
  have hlo : 4≤(Nat.card J).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h81
  apply genRank_le_two (by omega) J hp
  omega

end SymmetricSubgroupAsymptotics.PrimitiveFullThreeSylowOrdinaryGenerators
