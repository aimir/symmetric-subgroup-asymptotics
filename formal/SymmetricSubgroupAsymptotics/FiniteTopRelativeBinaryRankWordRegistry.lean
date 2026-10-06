import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.RelativeAmbientTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFiniteFrameSource

/-!
# Sparse word registries for finite top relative heads

The eight-block tops are not binary groups, so their complete normal menus
are best checked by conjugacy-class joins.  This wrapper adds the relative
binary head calculation to `FiniteNormalJoinWordRegistryData` and exposes
the same semantic bound as the point-indexed finite-frame registry.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {G I iota kappa : Type} [Group G] [Finite G]
  {c rank : ℕ} {representative : Fin c → G}
  (cover : FiniteConjugacyCardinalCover representative)
  (ambient : iota → G) (stateGenerators : I → kappa → G)

/-- A compact, locally checked complete normal registry with the relative
binary head bound attached to every generated state. -/
structure FiniteTopRelativeBinaryRankWordRegistry : Type 1 where
  [indexFinite : Finite I]
  data : FiniteNormalJoinWordRegistryData cover ambient stateGenerators
  head_le : ∀ i,
    letI : (Subgroup.closure (Set.range (stateGenerators i))).Normal :=
      (data.normality i).normal data.ambient_full
    Module.finrank (ZMod 2)
      (primeRelativeCharacters 2
        (Subgroup.closure (Set.range (stateGenerators i)))) ≤ rank

namespace FiniteTopRelativeBinaryRankWordRegistry

variable {cover ambient stateGenerators}
  (C : FiniteTopRelativeBinaryRankWordRegistry
    (rank := rank) cover ambient stateGenerators)

include C

/-- Sparse conjugacy joins cover every normal axis, so the stored row
calculations give the uniform top relative-head bound. -/
theorem bound (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ rank := by
  letI : Finite I := C.indexFinite
  obtain ⟨i, hi⟩ := C.data.complete N
  subst N
  letI : (Subgroup.closure (Set.range (stateGenerators i))).Normal :=
    (C.data.normality i).normal C.data.ambient_full
  exact C.head_le i

/-- The semantic top bound transports to the literal quotient top through
an exact group equivalence. -/
theorem bound_equiv {H : Type} [Group H] [Finite H]
    (e : G ≃* H) (N : Subgroup H) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ rank := by
  let M : Subgroup G := N.comap e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.comap inferInstance e.toMonoidHom
  have hmap : M.map e.toMonoidHom = N :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective N
  rw [(relativeCharacterAmbientCongr 2 e M N hmap).finrank_eq]
  exact C.bound M

end FiniteTopRelativeBinaryRankWordRegistry

end SymmetricSubgroupAsymptotics

end
