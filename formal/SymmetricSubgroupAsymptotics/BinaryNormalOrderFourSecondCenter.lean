import SymmetricSubgroupAsymptotics.PrimeNormalIntervalCharacters
import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalPresentation
import SymmetricSubgroupAsymptotics.NormalOrderTwo
import Mathlib.GroupTheory.Index

/-! An original normal subgroup of order four in a finite two-group lies
in the second upper centre. A nonzero original invariant character gives
a two-element bound on its actual mixed commutator, which is central. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics
local instance normalOrderFourSecondCenterFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {G : Type} [Group G] [Finite G]

theorem binary_normal_order_four_commutator_le_center
    (hG : IsPGroup 2 G) (L : Subgroup G) [L.Normal] (hcard : Nat.card L=4) :
    ⁅L,(⊤ : Subgroup G)⁆≤Subgroup.center G := by
  have hLne : L≠⊥ := L.one_lt_card_iff_ne_bot.mp (by rw [hcard];decide)
  obtain ⟨chi,_,_,hJproper,hJindex⟩ :=
    pGroup_normal_interval_character hG (⊥ : Subgroup G) L (bot_lt_iff_ne_bot.mpr hLne)
  let J := (AddMonoidHom.toMultiplicativeRight chi.1).ker.map L.subtype
  have hJL : J≤L := hJproper.le
  have hJcard : Nat.card J=2 := by
    have hc := (J.subgroupOf L).card_mul_index
    have he : Nat.card (J.subgroupOf L)=Nat.card J :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJL).toEquiv
    change Nat.card (J.subgroupOf L)*J.relIndex L=Nat.card L at hc
    rw [he,hJindex,hcard] at hc
    omega
  have hCJ : ⁅L,(⊤ : Subgroup G)⁆≤J :=
    ((primeRelativePowerCommutator_commutator_le 2 L).trans
      (primeRelativePowerCommutator_le_radical 2 L)).trans
        (primeRelativeRadical_le_mapped_character_ker 2 L chi)
  let C := ⁅L,(⊤ : Subgroup G)⁆
  have hc : Nat.card C≤2 := (Subgroup.card_le_of_le hCJ).trans_eq hJcard
  have hp : 0<Nat.card C := Nat.card_pos
  by_cases hsmall : Nat.card C≤1
  · have he : C=⊥ := C.eq_bot_of_card_le hsmall
    rw [show ⁅L,(⊤ : Subgroup G)⁆=⊥ from he]
    exact bot_le
  · exact NormalOrderTwo.le_center C (by omega)

theorem binary_normal_order_four_le_second_center
    (hG : IsPGroup 2 G) (L : Subgroup G) [L.Normal] (hcard : Nat.card L=4) :
    L≤(Subgroup.center (G ⧸ Subgroup.center G)).comap (QuotientGroup.mk' (Subgroup.center G)) := by
  intro l hl
  apply Subgroup.mem_center_iff.mpr
  intro x
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) x
  symm
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [←map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (binary_normal_order_four_commutator_le_center hG L hcard
      (Subgroup.commutator_mem_commutator hl (Subgroup.mem_top g)))

end SymmetricSubgroupAsymptotics
