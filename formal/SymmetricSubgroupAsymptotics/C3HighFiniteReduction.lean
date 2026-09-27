import SymmetricSubgroupAsymptotics.C3HighPrimitiveReduction
import SymmetricSubgroupAsymptotics.TernaryHighImprimitiveDegrees

/-!
# The high C3 branch reduces to bounded actual transitive actions

The literal image on each original orbit is transitive.  Combining the
primitive tail with the imprimitive five-degree theorem leaves precisely a
finite primitive action below degree 34 or an imprimitive action of degree
`6`, `9`, `12`, `18`, or `27`.  The normal subgroup and strict relative-head
witness are retained throughout.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The literal restriction image on an original orbit is transitive on that
same orbit.  Surjectivity is built into the range, so no abstract replacement
action is used. -/
theorem orbitImage_pretransitive {X : Type*}
    (H : Subgroup (Equiv.Perm X))
    (o : OrbitProfileFromOrbits.Orbit H) :
    MulAction.IsPretransitive (OrbitProfileFromOrbits.orbitImage H o) o.orbit := by
  constructor
  intro x y
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H x y
  exact ⟨⟨MulAction.toPermHom H o.orbit h, ⟨h, rfl⟩⟩, hh⟩

/-- Complete structural reduction of the high C3 orbit witness to the
bounded action domains. -/
theorem c3TrivialHigh_finite_action_reduction
    (hgen : PrimitiveNormalGeneratorInput)
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b : ℕ)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    ∃ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
      ∃ (N : Subgroup
          (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
        (hN : N.Normal),
        (3 * Nat.card o.orbit <
          20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) ∧
        ((MulAction.IsPreprimitive
            (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o)
            o.orbit ∧ Nat.card o.orbit < 34) ∨
          Nat.card o.orbit = 6 ∨ Nat.card o.orbit = 9 ∨
          Nat.card o.orbit = 12 ∨ Nat.card o.orbit = 18 ∨
          Nat.card o.orbit = 27) := by
  obtain ⟨o, N, hN, hhigh, hprimitiveReduction⟩ :=
    c3TrivialHigh_primitive_reduction hgen b P H hH
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  refine ⟨o, N, hN, hhigh, ?_⟩
  by_cases hp : MulAction.IsPreprimitive A o.orbit
  · left
    refine ⟨hp, ?_⟩
    rcases hprimitiveReduction with hsmall | himprimitive
    · exact hsmall
    · exact False.elim (himprimitive hp)
  · right
    exact ternaryHigh_imprimitive_degree_menu hChief hWeight hPrimitive h18 N hp hhigh

end SymmetricSubgroupAsymptotics

end
