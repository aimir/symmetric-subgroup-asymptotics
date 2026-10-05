import SymmetricSubgroupAsymptotics.FiniteConjugacyCentralizerCoordinates
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.BinaryPairFrames

/-!
# Selected finite witness schema for one six-pair action

The recovery exporter is required to emit exactly one of the 182 retained
degree-twelve actions at a time.  This structure is the narrow Lean target
for that output.  It retains the actual twelve-point pair frame, proves the
selected conjugacy cover from centralizer coordinates, and proves the normal
registry from local join words.  No asserted class cover or normal-list
completeness flag is accepted.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {c n a k : ℕ}
    {G : Subgroup (Equiv.Perm (Fin 12))}
    {ambient : Fin a → G}
    {representative : Fin c → G}
    {stateGenerators : Fin n → Fin k → G}

/-- Complete structural certificate for one selected six-pair action.  The
normal generator width may be padded by identity rows, keeping emitted chunk
types uniform within that action. -/
structure PrimitiveAffineDegreeTwoSixPairSelectedWitness
    (G : Subgroup (Equiv.Perm (Fin 12)))
    (ambient : Fin a → G)
    (representative : Fin c → G)
    (stateGenerators : Fin n → Fin k → G) where
  pairFrame : BinaryPairFrame G (Fin 6)
  conjugacy : FiniteConjugacyCentralizerCoordinateChunk representative 6
  centralizer_top : ∀ i,
    (conjugacy.centralizer i).top =
      pairFrame.top.comp
        (Subgroup.centralizer
          ({representative i} : Set G)).subtype
  normalRegistry : FiniteNormalJoinWordRegistryData
    conjugacy.toCardinalCover ambient stateGenerators

namespace PrimitiveAffineDegreeTwoSixPairSelectedWitness

variable
    (D : PrimitiveAffineDegreeTwoSixPairSelectedWitness
      G ambient representative stateGenerators)

include D

/-- The selected centralizer chunks prove actual conjugacy coverage in the
literal twelve-point action. -/
noncomputable def conjugacyCover :
    FiniteConjugacyCardinalCover representative :=
  D.conjugacy.toCardinalCover

/-- Every literal normal subgroup occurs among the emitted generated states.
This is a theorem of the word chunks, not a producer assertion. -/
theorem normal_complete (N : Subgroup G) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  D.normalRegistry.complete N

end PrimitiveAffineDegreeTwoSixPairSelectedWitness

end SymmetricSubgroupAsymptotics

end
