import SymmetricSubgroupAsymptotics.NormalCoprimeTransitiveAction
import Mathlib.GroupTheory.Transfer

/-! A cyclic Sylow2 subgroup in a faithful transitive action of2-power
degree forces the whole group to be binary. Burnside's actual normal
complement has odd order; its original point orbits are therefore trivial. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
  [FaithfulSMul G X] [MulAction.IsPretransitive G X]

/-- The minimum-prime equality is an arithmetic premise about the actual
group order, supplied automatically by any nontrivial binary subgroup. -/
theorem isPGroup_of_cyclic_sylow_two (P : Sylow 2 G) (hcyclic : IsCyclic P)
    (hmin : (Nat.card G).minFac = 2) (d : ℕ) (hdegree : Nat.card X = 2 ^ d) :
    IsPGroup 2 G := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hnorm := hcyclic.normalizer_le_centralizer hmin
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

end SymmetricSubgroupAsymptotics
end
