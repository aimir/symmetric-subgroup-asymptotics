import SymmetricSubgroupAsymptotics.FiniteCentralizerNecessaryWhitelist
import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords
import SymmetricSubgroupAsymptotics.External.CFSG.Certificates.Mathieu12.Certificates.WittDesign
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic.NormNum

/-! Reusable original-M12 centralizer upper certificates. An ambient
centralizer chart and necessary Witt-block rejection suffice. Accepted
codes need no original membership witnesses or commuting-word lower bound.
The selected y profile has ambient centralizer1944, not the whole group.
No concrete whitelist or upper class bound is assumed at a global endpoint. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveWittCentralizerWhitelist
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords
open M12Certificates.WittDesign

theorem original_centralizer_card_le_of_bad_blocks
    {I : Type*} (a : M12) (chart : I → Perm12)
    (complete : ∀ z : Perm12, z * a.val = a.val * z → ∃ i, chart i = z)
    (accepted : Finset I)
    (bad_block : ∀ i : I, chart i * a.val = a.val * chart i → i ∉ accepted →
      ∃ k : Fin 132, blockMap (chart i) (wittBlockAt k) ∉ wittBlocks) :
    Nat.card (Subgroup.centralizer ({a} : Set M12)) ≤ accepted.card := by
  apply FiniteCentralizerNecessaryWhitelist.centralizer_card_le_whitelist
    M12Subgroup.subtype Subtype.val_injective a chart complete
    PreservesWittBlocks M12_preserves_wittBlocks accepted
  intro i hc hpreserves
  by_contra hnot
  obtain ⟨k,hk⟩ := bad_block i hc hnot
  exact hk (hpreserves.1 _
    (mem_wittBlockList_of_mem_wittBlocks (wittBlockAt_mem k)))

theorem y_ambient_centralizer_card :
    Nat.card (Subgroup.centralizer ({y.val} : Set Perm12)) = 1944 := by
  rw [Equiv.Perm.nat_card_centralizer,y_cycleType]
  norm_num [Nat.factorial]

theorem y_centralizer_card_le_of_bad_blocks
    (chart : Fin 1944 → Perm12)
    (complete : ∀ z : Perm12, z * y.val = y.val * z → ∃ i, chart i = z)
    (accepted : Finset (Fin 1944))
    (bad_block : ∀ i : Fin 1944, chart i * y.val = y.val * chart i → i ∉ accepted →
      ∃ k : Fin 132, blockMap (chart i) (wittBlockAt k) ∉ wittBlocks) :
    Nat.card (Subgroup.centralizer ({y} : Set M12)) ≤ accepted.card :=
  original_centralizer_card_le_of_bad_blocks y chart complete accepted bad_block

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveWittCentralizerWhitelist
