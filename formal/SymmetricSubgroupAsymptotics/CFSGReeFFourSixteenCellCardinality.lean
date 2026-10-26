import SymmetricSubgroupAsymptotics.CFSGReeFFourSixteenCellEquivalence
import SymmetricSubgroupAsymptotics.CFSGReeFFourShortInversionCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourWeightedBruhatNumerics
import Mathlib.GroupTheory.Coset.Card

/-! Exact cardinality of the actual original fixed group from its proved
sixteen-cell bijection. The original derived/full-centre quotient order
only needs to divide this cardinality; no trivial-centre assertion is
used to obtain the q8 prime11 exclusion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSixteenCellCardinality
open CFSGReeFFourSixteenCellEquivalence CFSGReeFFourShortInversionCardinality
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedAmbientHom
open CFSGReeFFourFixedBorelCardinality CFSGReeFFourShortPairedWeylMenu

private instance fixedFinite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

/-- This is the cardinality of the SAME original fixed group, before
passing to its derived subgroup or the full central quotient. -/
theorem fixed_order_eq_weighted (m : ℕ) :
    Nat.card (originalModelFixed m) = (2^(2*m+1))^12*(2^(2*m+1)-1)^2*
      CFSGReeFFourWeightedBruhatNumerics.weightedMenu (2^(2*m+1)) := by
  calc
    _=Nat.card (Σ i : Fin 16, Cell m i) :=
      (Nat.card_congr (Equiv.ofBijective (cellMap m) (cellMap_bijective m))).symm
    _=∑ i : Fin 16, Nat.card (Cell m i) := Nat.card_sigma
    _=Nat.card (fixedBorel m)*∑ i : Fin 16, (2^(2*m+1))^(inversionWeight i) := by
      simp_rw [Cell,Nat.card_prod,short_inversion_card]
      rw [Finset.mul_sum]
    _=_ := by rw [fixedBorel_card,weighted_short_menu]

theorem original_card_dvd_fixed_card (m : ℕ) :
    Nat.card (CFSG.Models.ReeF4 m) ∣ Nat.card (originalModelFixed m) := by
  rw [Nat.card_congr (originalReeEquiv m).toEquiv]
  change Nat.card ((commutator (originalModelFixed m)) ⧸
      Subgroup.center (commutator (originalModelFixed m))) ∣ Nat.card (originalModelFixed m)
  exact (Subgroup.card_quotient_dvd_card
    (Subgroup.center (commutator (originalModelFixed m)))).trans
      (Subgroup.card_subgroup_dvd_card (commutator (originalModelFixed m)))

theorem eleven_not_dvd_fixed_fieldEight : ¬11 ∣ Nat.card (originalModelFixed 1) := by
  rw [fixed_order_eq_weighted,CFSGReeFFourWeightedBruhatNumerics.weightedMenu_factor]
  decide +kernel

theorem eleven_not_dvd_original_fieldEight : ¬11 ∣ Nat.card (CFSG.Models.ReeF4 1) := by
  intro h
  exact eleven_not_dvd_fixed_fieldEight (h.trans (original_card_dvd_fixed_card 1))

end SymmetricSubgroupAsymptotics.CFSGReeFFourSixteenCellCardinality
