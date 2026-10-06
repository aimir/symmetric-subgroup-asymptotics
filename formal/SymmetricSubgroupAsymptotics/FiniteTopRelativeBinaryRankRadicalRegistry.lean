import SymmetricSubgroupAsymptotics.FiniteTopRelativeBinaryRankWordRegistry
import SymmetricSubgroupAsymptotics.PrimeRelativeRadicalWords

/-!
# Relative binary heads from finite radical rows

The eight-frame computation already constructs the exact subgroup
`[N,T] N²` for every normal state `N`.  This wrapper converts those checked
radical identifications and subgroup cardinalities into the relative-head
field of `FiniteTopRelativeBinaryRankWordRegistry`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {G I ι κ : Type} [Group G] [Finite G]
  {c rank : ℕ} {representative : Fin c → G}
  {cover : FiniteConjugacyCardinalCover representative}
  {ambient : ι → G} {stateGenerators : I → κ → G}

/-- A complete normal-word registry whose exact relative binary radical is
another recorded state.  The cardinal factorization retains the actual
normal and radical subgroup orders; `headRank` is derived from it rather
than trusted as the desired conclusion. -/
structure FiniteTopRelativeBinaryRankRadicalRegistry
    (data : FiniteNormalJoinWordRegistryData
      cover ambient stateGenerators) : Type 1 where
  [indexFinite : Finite I]
  radicalIndex : I → I
  headRank : I → ℕ
  headRank_le : ∀ i, headRank i ≤ rank
  radical_eq : ∀ i,
    letI : (Subgroup.closure (Set.range (stateGenerators i))).Normal :=
      (data.normality i).normal data.ambient_full
    letI : (Subgroup.closure
        (Set.range (stateGenerators (radicalIndex i)))).Normal :=
      (data.normality (radicalIndex i)).normal data.ambient_full
    primeRelativeRadical 2
        (Subgroup.closure (Set.range (stateGenerators i))) =
      Subgroup.closure (Set.range (stateGenerators (radicalIndex i)))
  card_factorization : ∀ i,
    Nat.card (Subgroup.closure (Set.range (stateGenerators i))) =
      2 ^ headRank i *
        Nat.card (Subgroup.closure
          (Set.range (stateGenerators (radicalIndex i))))

namespace FiniteTopRelativeBinaryRankRadicalRegistry

variable {data : FiniteNormalJoinWordRegistryData
  cover ambient stateGenerators}
  (C : FiniteTopRelativeBinaryRankRadicalRegistry
    (rank := rank) data)

include C

/-- The finite radical rows supply the exact relative head at every normal
state, hence the uniform rank bound. -/
theorem head_le (i : I) :
    letI : (Subgroup.closure (Set.range (stateGenerators i))).Normal :=
      (data.normality i).normal data.ambient_full
    Module.finrank (ZMod 2)
      (primeRelativeCharacters 2
        (Subgroup.closure (Set.range (stateGenerators i)))) ≤ rank := by
  letI : (Subgroup.closure (Set.range (stateGenerators i))).Normal :=
    (data.normality i).normal data.ambient_full
  letI : (Subgroup.closure
      (Set.range (stateGenerators (C.radicalIndex i)))).Normal :=
    (data.normality (C.radicalIndex i)).normal data.ambient_full
  have heq := primeRelativeHead_eq_of_radical_card 2
    (Subgroup.closure (Set.range (stateGenerators i)))
    (Subgroup.closure
      (Set.range (stateGenerators (C.radicalIndex i))))
    (C.headRank i) (C.radical_eq i) (C.card_factorization i)
  rw [heq]
  exact C.headRank_le i

/-- Assemble the existing sparse word-registry interface. -/
noncomputable def toWordRegistry :
    FiniteTopRelativeBinaryRankWordRegistry
      (rank := rank) cover ambient stateGenerators where
  indexFinite := C.indexFinite
  data := data
  head_le := C.head_le

end FiniteTopRelativeBinaryRankRadicalRegistry
end SymmetricSubgroupAsymptotics

end
