import SymmetricSubgroupAsymptotics.FiniteNormalJoinRegistry
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordCertificate

/-!
# Assemble a sparse normal registry from word chunks

This is the Lean consumer for the normal-state part of one selected affine
action witness.  The generated action file supplies only short generator
tuples and local word certificates.  The generic theorem constructs the
exact `FiniteNormalJoinRegistry`; its already checked `complete` theorem then
recovers every literal normal subgroup.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G I ι κ : Type*} [Group G] [Finite G] {c : ℕ}
    {representative : Fin c → G}

/-- Proof-carrying normal-state witness for one selected literal action.
The generator width `κ` is fixed per emitted action and may be padded by
identity generators. -/
structure FiniteNormalJoinWordRegistryData
    (C : FiniteConjugacyCardinalCover representative)
    (ambient : ι → G) (stateGenerators : I → κ → G) where
  ambient_full : Subgroup.closure (Set.range ambient) = ⊤
  normality : ∀ i,
    FiniteNormalityWordCertificate ambient (stateGenerators i)
  bottom : I
  bottom_eq :
    Subgroup.closure (Set.range (stateGenerators bottom)) = ⊥
  child : I → Fin c → I
  transition : ∀ i j,
    FiniteNormalJoinTransitionCertificate
      (stateGenerators i) (representative j)
      (stateGenerators (child i j))

namespace FiniteNormalJoinWordRegistryData

variable {C : FiniteConjugacyCardinalCover representative}
    {ambient : ι → G} {stateGenerators : I → κ → G}
    (D : FiniteNormalJoinWordRegistryData C ambient stateGenerators)

include D

/-- Install the exact generated subgroups and discharge every registry field
from the emitted local word chunks. -/
noncomputable def toRegistry :
    FiniteNormalJoinRegistry C
      (fun i => Subgroup.closure (Set.range (stateGenerators i))) where
  normal i := (D.normality i).normal D.ambient_full
  bottom := D.bottom
  bottom_eq := D.bottom_eq
  child := D.child
  child_eq i j := by
    letI : (Subgroup.closure
        (Set.range (stateGenerators (D.child i j)))).Normal :=
      (D.normality (D.child i j)).normal D.ambient_full
    exact (D.transition i j).join_eq.symm

/-- Every literal normal subgroup is one of the emitted generated states.
The result uses no asserted completeness flag from the producer. -/
theorem complete (N : Subgroup G) [N.Normal] :
    ∃ i, Subgroup.closure (Set.range (stateGenerators i)) = N :=
  D.toRegistry.complete N

end FiniteNormalJoinWordRegistryData

end SymmetricSubgroupAsymptotics

end
