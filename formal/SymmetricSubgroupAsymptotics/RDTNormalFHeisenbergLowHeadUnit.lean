import SymmetricSubgroupAsymptotics.RDTNormalFHeisenbergUnitAxisEnvelope
import SymmetricSubgroupAsymptotics.BinaryHeisenbergRankFiveCards

/-! One proof treats every original head-one Heisenberg kernel. Only the
small linear joint-axis envelope varies with its coordinate chart; no
normal-subgroup, lift, or extension-class census is needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 8))
open BinaryHeisenbergEightNaturalHeads BinaryHeisenbergCoordinateTemplate

theorem heisenberg_rank_five_derived_le_kernel_card
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = H) :
    Nat.card U = 32 * Nat.card F.kernelSpace ∧
      Nat.card (commutator U) ≤ Nat.card F.kernelSpace := by
  have ht : Nat.card F.top.range = 32 :=
    (Nat.card_congr (MulEquiv.subgroupCongr hH).toEquiv).trans
      BinaryMenuCayley8T22.exact_card
  have hc := F.kernelSpace_card_mul_top
  rw [ht] at hc
  have hu : Nat.card U = 32 * Nat.card F.kernelSpace := by nlinarith
  have ha : 32 ≤ Nat.card (Abelianization U) :=
    (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hrank).trans
      (pGroup_pow_genRank_le_abelianization_card 2 hU)
  have hd := (commutator U).card_eq_card_quotient_mul_card_subgroup
  change Nat.card U = Nat.card (Abelianization U) * Nat.card (commutator U) at hd
  rw [hu] at hd
  exact ⟨hu, by nlinarith⟩

theorem heisenberg_low_head_unit_normalF_packet
    (hU : IsPGroup 2 U) (hrank : 5 ≤ MarkedC4.genRank U)
    (hH : F.top.range = H)
    (K R : Submodule (ZMod 2) V) (hK : F.kernelSpace = K)
    (hR : F.ambientAxis (primeRelativeRadical 2 F.top.ker) = R)
    (hRK : R ≤ K) (hcard : Nat.card K = 2 * Nat.card R)
    (henvelope : ∀ A : Subrepresentation rho, A.toSubmodule ≤ K →
      JointAxisEnvelope K R A.toSubmodule (Nat.card R))
    (N : Subgroup U) [N.Normal]
    (hnonab : ¬ ∀ a b : U ⧸ N, a * b = b * a) :
    ∃ W : Subgroup (U ⧸ N), W.Normal ∧
      MarkedC4.ActualNormalFMarkedPeel.commutatorLog W +
        MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 8 ∧
      MarkedC4.ActualNormalFMarkedPeel.centralLog W ≤ 4 := by
  obtain ⟨hu, hd⟩ := F.heisenberg_rank_five_derived_le_kernel_card hU hrank hH
  rw [hK, hcard] at hu hd
  exact F.heisenberg_unit_normalF_of_doubled_axis_envelopes hU hH K R hK.symm hRK
    (F.radical_coordinate_le_derived R hR) (Nat.card R) hd
    (by omega) (by omega) henvelope N hnonab

end SymmetricSubgroupAsymptotics.BinaryPairFrame
