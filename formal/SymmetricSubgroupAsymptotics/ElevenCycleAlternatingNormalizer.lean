import SymmetricSubgroupAsymptotics.FiniteCyclicNormalizerCardBound
import SymmetricSubgroupAsymptotics.ElevenCycleOddInverter

/-! An order110 subgroup normalizing an eleven-cycle necessarily contains
an odd permutation. The proof counts the actual conjugation homomorphism
and transports one explicitly checked odd inverter. -/
set_option autoImplicit false
noncomputable section
open Equiv
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- Every order-eleven cyclic subgroup of the twelve-point symmetric group
has normalizer order at most110. -/
theorem elevenCycle_normalizer_card_le
    (g : Perm (Fin 12)) (hg : orderOf g=11) :
    Nat.card (Subgroup.normalizer (Subgroup.zpowers g : Set (Perm (Fin 12)))) ≤110 := by
  have h := prime_order_normalizer_card_le g (by decide : Nat.Prime 11) hg
  have hc : Nat.card (Subgroup.centralizer (Subgroup.zpowers g : Set (Perm (Fin 12))))=11 := by
    rw [Subgroup.zpowers_eq_closure,Subgroup.centralizer_closure,
      ElevenCycleOddInverter.centralizer_card g hg]
  simpa only [hc] using h

/-- The odd witness really belongs to the actual cyclic normalizer. -/
theorem elevenCycle_normalizer_has_odd
    (g : Perm (Fin 12)) (hg : orderOf g=11) :
    ∃ a∈Subgroup.normalizer (Subgroup.zpowers g : Set (Perm (Fin 12))),
      Perm.sign a = -1 := by
  obtain ⟨a,ha,hs⟩ := ElevenCycleOddInverter.exists_odd_inverter g hg
  refine ⟨a,Subgroup.mem_normalizer_fintype ?_,hs⟩
  intro x hx
  obtain ⟨z,rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [←conj_zpow,ha]
  exact (Subgroup.zpowers g).zpow_mem ((Subgroup.zpowers g).inv_mem
    (Subgroup.mem_zpowers g)) z

/-- This is the precise obstruction needed for the degree12 point
stabilizer of a hypothetical simple group of order1320. -/
theorem no_even_order110_elevenCycle_normalizer
    (H : Subgroup (Perm (Fin 12))) (hcard : Nat.card H=110)
    (g : Perm (Fin 12)) (hg : orderOf g=11)
    (hn : H≤Subgroup.normalizer (Subgroup.zpowers g : Set (Perm (Fin 12))))
    (he : ∀ h∈H,Perm.sign h=1) : False := by
  have heq := Subgroup.eq_of_le_of_card_ge hn
    ((elevenCycle_normalizer_card_le g hg).trans_eq hcard.symm)
  obtain ⟨a,ha,hs⟩ := elevenCycle_normalizer_has_odd g hg
  have haH : a∈H := by rw [heq]; exact ha
  have h := (he a haH).symm.trans hs
  norm_num at h

end SymmetricSubgroupAsymptotics
