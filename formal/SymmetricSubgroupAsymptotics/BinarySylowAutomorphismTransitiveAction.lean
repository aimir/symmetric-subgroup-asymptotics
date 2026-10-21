import SymmetricSubgroupAsymptotics.NormalCoprimeTransitiveAction
import Mathlib.GroupTheory.Transfer

/-! Abelian Sylow2 subgroups with binary automorphism groups centralize
in their normalizers: the actual normalizer/centralizer quotient is both
binary and odd. Burnside transfer then retains the original faithful action. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open Subgroup

variable {G X : Type*} [Group G] [Finite G]

theorem sylow_normalizer_centralizes_of_binary_automorphisms (P : Sylow 2 G)
    (hcomm : IsMulCommutative P) (hAut : IsPGroup 2 (MulAut P)) :
    normalizer P ≤ centralizer (P : Set G) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI := hcomm
  -- This relative-index argument specializes the Apache-2.0 mathlib
  -- GroupTheory.Transfer proof of IsCyclic.normalizer_le_centralizer.
  have key := card_dvd_of_injective _ (QuotientGroup.kerLift_injective P.normalizerMonoidHom)
  rw [normalizerMonoidHom_ker,←index,←relIndex] at key
  obtain ⟨k,hk⟩ := hAut.exists_card_eq
  rw [hk] at key
  apply relIndex_eq_one.mp
  apply Nat.eq_one_of_dvd_coprimes _ dvd_rfl key
  refine Nat.Coprime.pow_right k ?_
  apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_of_le_left _ P.le_centralizer)
  apply Nat.Coprime.coprime_dvd_left (relIndex_dvd_index_of_le P.le_normalizer)
  rw [Nat.coprime_comm,Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 2)]
  exact P.not_dvd_index

variable [Finite X] [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]

theorem isPGroup_of_abelian_sylow_binary_automorphisms (P : Sylow 2 G)
    (hcomm : IsMulCommutative P) (hAut : IsPGroup 2 (MulAut P))
    (d : ℕ) (hdegree : Nat.card X = 2 ^ d) : IsPGroup 2 G := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hnorm := sylow_normalizer_centralizes_of_binary_automorphisms P hcomm hAut
  let f := MonoidHom.transferSylow P hnorm
  let K := f.ker
  have hodd : ¬2 ∣ Nat.card K := MonoidHom.not_dvd_card_ker_transferSylow P hnorm
  have hcoprime : Nat.Coprime (Nat.card K) (Nat.card X) := by
    rw [hdegree]
    exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 2)).mpr hodd).symm.pow_right d
  have hK : K = ⊥ := normal_eq_bot_of_card_coprime_degree (X := X) K hcoprime
  have hsup := (MonoidHom.ker_transferSylow_isComplement' P hnorm).sup_eq_top
  have htop : (P : Subgroup G) = ⊤ := by
    change K ⊔ (P : Subgroup G) = ⊤ at hsup
    simpa only [hK,bot_sup_eq] using hsup
  have hp : IsPGroup 2 (⊤ : Subgroup G) := htop ▸ P.2
  exact hp.of_equiv Subgroup.topEquiv

theorem exists_larger_sylow_of_binary_automorphism_seed (H : Subgroup G)
    (hH : IsPGroup 2 H) (hcomm : IsMulCommutative H) (hAut : IsPGroup 2 (MulAut H))
    (d : ℕ) (hdegree : Nat.card X = 2 ^ d) (hnot : ¬IsPGroup 2 G) :
    ∃ P : Sylow 2 G,H ≤ P ∧ Nat.card H < Nat.card P := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨P,hHP⟩ := hH.exists_le_sylow
  refine ⟨P,hHP,?_⟩
  by_contra hn
  have heq : H = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hHP (le_of_not_gt hn)
  have hpcomm : IsMulCommutative P := by
    change IsMulCommutative ↥(P : Subgroup G)
    rw [←heq]
    exact hcomm
  have hpAut : IsPGroup 2 (MulAut P) := by
    change IsPGroup 2 (MulAut ↥(P : Subgroup G))
    rw [←heq]
    exact hAut
  exact hnot (isPGroup_of_abelian_sylow_binary_automorphisms (X := X)
    P hpcomm hpAut d hdegree)

end SymmetricSubgroupAsymptotics
end
