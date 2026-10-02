import SymmetricSubgroupAsymptotics.Non2PreE7SmallC3PacketNumerics

/-!
# Exact removal of the complete degree-three packet

The final no-pair/no-`C3` residual is the disjoint union of the packet whose
every violating orbit has degree three and the complementary residual, which
has a violating orbit of degree at least four.  This file records that split
at the level of the literal permutation subgroups and hence at the level of
the benchmark-normalized ratios.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- The exact complement of the complete degree-three packet inside the
no-pair/no-`C3` residual. -/
def PreE7NoPairNoC3LargeResidualSubgroupSet (n : ℕ) :
    Set (Subgroup (Equiv.Perm (Fin n))) :=
  {H | ∃ hH : H ∈ PreE7NoPairNoC3ResidualSubgroupSet n,
    ¬ AllPreE7ViolationOrbitsDegreeThree H}

/-- Exact normalized size of the residual complementary to the complete
degree-three packet. -/
def preE7NoPairNoC3LargeResidualRatio (n : ℕ) : ℝ :=
  Nat.card (PreE7NoPairNoC3LargeResidualSubgroupSet n) / exactBenchmark n

private def residualSumPacketLargeEquiv (n : ℕ) :
    PreE7NoPairNoC3ResidualSubgroupSet n ≃
      PreE7SmallC3PacketSubgroupSet n ⊕
        PreE7NoPairNoC3LargeResidualSubgroupSet n := by
  let split := (Equiv.sumCompl
    (fun G : PreE7NoPairNoC3ResidualSubgroupSet n =>
      AllPreE7ViolationOrbitsDegreeThree G.1)).symm
  refine split.trans (Equiv.sumCongr (Equiv.refl _) ?_)
  exact
    { toFun := fun G => ⟨G.1.1, ⟨G.1.2, G.2⟩⟩
      invFun := fun H => ⟨⟨H.1, H.2.choose⟩, H.2.choose_spec⟩
      left_inv := by
        intro G
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro H
        apply Subtype.ext
        rfl }

theorem preE7NoPairNoC3Residual_card_eq_packet_add_large (n : ℕ) :
    Nat.card (PreE7NoPairNoC3ResidualSubgroupSet n) =
      Nat.card (PreE7SmallC3PacketSubgroupSet n) +
        Nat.card (PreE7NoPairNoC3LargeResidualSubgroupSet n) := by
  rw [Nat.card_congr (residualSumPacketLargeEquiv n), Nat.card_sum]

/-- Exact ratio identity used to splice the global degree-three packet into
the remaining width-at-least-four recurrence. -/
theorem preE7NoPairNoC3ResidualRatio_eq_packet_add_large (n : ℕ) :
    preE7NoPairNoC3ResidualRatio n =
      preE7SmallC3PacketRatio n + preE7NoPairNoC3LargeResidualRatio n := by
  rw [preE7NoPairNoC3ResidualRatio_eq_subgroupSet,
    preE7SmallC3PacketRatio, preE7NoPairNoC3LargeResidualRatio,
    preE7NoPairNoC3Residual_card_eq_packet_add_large]
  push_cast
  ring

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
