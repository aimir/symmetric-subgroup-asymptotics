import SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate
import SymmetricSubgroupAsymptotics.BinaryNormalCharacterCriterion
import SymmetricSubgroupAsymptotics.BinaryNormalTransport8

/-! Finite-entry coverage is separate from the analytic fusion theorem.
Pair entries retain an actual physical frame, generators, cut and cover.
Character entries retain the actual quotient's full central involution
space and strict integer criterion. The three width-eight transports are
exactly the independently checked physical carrier charts. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

def binaryEightTransportChart (i : Fin 3) : CheckedPermutationCarrier 8 16 :=
  ![BinaryChart8T16.chart,BinaryChart8T20.chart,BinaryChart8T21.chart] i

/-- Each selected transport uses a full block on the same eight original
points, whose actual range is a transitive group of order 64. The carrier
and its exterior correlations are still those of the literal chart. -/
theorem binaryEightTransportChart_full_block (i : Fin 3) :
    ∃ B : Subgroup (Equiv.Perm (Fin 8)), ∃ e : Fin 8 ↪ Fin 8,
      ∃ f : (binaryEightTransportChart i).carrier →* Equiv.Perm (Fin 8),
        f.range=B ∧ (∀ x, ∃ y, e y=x) ∧
        (∀ (g : (binaryEightTransportChart i).carrier) y, (g : Equiv.Perm (Fin 8)) (e y)=e (f g y)) ∧
        Nat.card B=64 ∧ ∀ x y : Fin 8, ∃ g : B, (g : Equiv.Perm (Fin 8)) x=y := by
  fin_cases i
  · exact ⟨Subgroup.closure (Set.range BinaryChart8T16.block0BaseGenerators),
      BinaryChart8T16.block0.embedding,BinaryChart8T16.block0.hom,
      BinaryChart8T16.block0_range,BinaryChart8T16.blocks_cover,
      BinaryChart8T16.block0.hom_intertwine,BinaryChart8T16.block0_base_card,
      BinaryChart8T16.block0_base_transitive⟩
  · exact ⟨Subgroup.closure (Set.range BinaryChart8T20.block0BaseGenerators),
      BinaryChart8T20.block0.embedding,BinaryChart8T20.block0.hom,
      BinaryChart8T20.block0_range,BinaryChart8T20.blocks_cover,
      BinaryChart8T20.block0.hom_intertwine,BinaryChart8T20.block0_base_card,
      BinaryChart8T20.block0_base_transitive⟩
  · exact ⟨Subgroup.closure (Set.range BinaryChart8T21.block0BaseGenerators),
      BinaryChart8T21.block0.embedding,BinaryChart8T21.block0.hom,
      BinaryChart8T21.block0_range,BinaryChart8T21.blocks_cover,
      BinaryChart8T21.block0.hom_intertwine,BinaryChart8T21.block0_base_card,
      BinaryChart8T21.block0_base_transitive⟩

/-- This predicate certifies the finite menu alternatives on the exact
original normal. Its character branch still needs the separately proved
faithful-character counting envelope before analytic fusion can use it. -/
def BinaryFiniteEntry8 (U : Subgroup (Equiv.Perm (Fin 8)))
    (N : Subgroup U) [N.Normal] : Prop :=
  Nonempty (BinaryPhysicalPairCertificate U N) ∨
  Nonempty (BinaryNormalCharacterCriterion (U ⧸ N) 8) ∨
  ∃ i, (binaryEightTransportChart i).source=U ∧
    (binaryEightTransportChart i).axis=N.map U.subtype

end SymmetricSubgroupAsymptotics
