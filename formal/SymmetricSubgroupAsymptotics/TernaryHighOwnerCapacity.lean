import SymmetricSubgroupAsymptotics.TernaryHighOwnedActionDegrees
import SymmetricSubgroupAsymptotics.DegreeSixBinaryBlockOwner
import SymmetricSubgroupAsymptotics.DegreeTwelveTopGeometry
import SymmetricSubgroupAsymptotics.C1TernaryPrimeBaseOwner
import SymmetricSubgroupAsymptotics.C1BinaryNineTopOwner
import SymmetricSubgroupAsymptotics.C1FiniteOwnerTransport
import SymmetricSubgroupAsymptotics.C3HighOrbitDichotomy

/-!
# Earlier ownership or capacity on the high ternary frontier

The global ternary stability inputs reduce every strict failure of the
`3/20` capacity inequality to degrees three, four, six, nine, twelve or
twenty-seven.  The first, fourth and sixth degrees are already 3-group
owners, degree four is the natural `A₄` owner, degree six has one of the two
intrinsic binary owners, and the two degree-twelve minimal-block orientations
install the prime-base or nine-translation owner.

This file packages that reduction as the exact owner-or-capacity dichotomy
needed by the outside-action recurrence.  The four global stability
propositions remain explicit hypotheses.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The already constructed structural owners which absorb every strict
failure of the ternary `3/20` capacity inequality. -/
def TernaryHighEarlierOwner (A Ω : Type) [Group A] [MulAction A Ω] : Prop :=
  IsPGroup 3 A ∨
    IsNaturalA4Action A Ω ∨
      Nonempty (C1OddIndexTwoOwnerWitness A) ∨
        Nonempty (C1CyclicBinaryModuleOwnerWitness A) ∨
          IsC1TernaryPrimeBaseOwner A ∨
            IsC1BinaryNineTopOwner A Ω

namespace TernaryHighEarlierOwner

variable {Ω Ξ : Type} (e : Ω ≃ Ξ)
    (A : Subgroup (Equiv.Perm Ω))

private abbrev groupEquiv : A ≃* relabelSubgroup e A :=
  e.permCongrHom.subgroupMap A

private theorem point_equivariant (a : A) (x : Ω) :
    e (a • x) = (groupEquiv e A a) • e x := by
  change e ((a : Equiv.Perm Ω) x) =
    e ((a : Equiv.Perm Ω) (e.symm (e x)))
  rw [e.symm_apply_apply]

/-- The natural four-point A4 owner is unchanged by an actual relabelling of
its points and the induced equivalence of its permutation subgroup. -/
theorem naturalA4_relabel
    (h : IsNaturalA4Action A Ω) :
    IsNaturalA4Action (relabelSubgroup e A) Ξ := by
  obtain ⟨c, hc⟩ := h
  refine ⟨e.symm.trans c, ?_⟩
  have hhom (a : A) :
      labelledActionHom (A := relabelSubgroup e A) (e.symm.trans c)
          (groupEquiv e A a) =
        labelledActionHom (A := A) c a := by
    apply Equiv.ext
    intro x
    obtain ⟨y, rfl⟩ := c.surjective x
    calc
      labelledActionHom (A := relabelSubgroup e A) (e.symm.trans c)
          (groupEquiv e A a) (c y) =
        labelledActionHom (A := relabelSubgroup e A) (e.symm.trans c)
          (groupEquiv e A a) ((e.symm.trans c) (e y)) := by simp
      _ = (e.symm.trans c) ((groupEquiv e A a) • e y) :=
        labelledActionHom_apply (A := relabelSubgroup e A)
          (e.symm.trans c) (groupEquiv e A a) (e y)
      _ = c (a • y) := by
        change c (e.symm ((groupEquiv e A a : Equiv.Perm Ξ) (e y))) = _
        apply congrArg c
        apply e.injective
        rw [e.apply_symm_apply]
        exact (point_equivariant e A a y).symm
      _ = labelledActionHom (A := A) c a (c y) :=
        (labelledActionHom_apply (A := A) c a y).symm
  have himage :
      labelledActionImage (A := relabelSubgroup e A) (e.symm.trans c) =
        labelledActionImage (A := A) c := by
    apply le_antisymm
    · rintro p ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := (groupEquiv e A).surjective b
      exact ⟨a, (hhom a).symm⟩
    · rintro p ⟨a, rfl⟩
      exact ⟨groupEquiv e A a, hhom a⟩
  rw [himage, hc]

/-- Every structural owner in the high-ternary disjunction survives point
relabelling.  The nine-top branch transports the literal binary base, its
whole quotient action, all nine translations, and the conjugation identity. -/
theorem relabel (h : TernaryHighEarlierOwner A Ω) :
    TernaryHighEarlierOwner (relabelSubgroup e A) Ξ := by
  rcases h with hP | hA4 | hOdd | hCyclic | hPrime | hNine
  · exact Or.inl (hP.of_equiv (groupEquiv e A))
  · exact Or.inr (Or.inl (naturalA4_relabel e A hA4))
  · obtain ⟨W⟩ := hOdd
    exact Or.inr (Or.inr (Or.inl ⟨W.map (groupEquiv e A)⟩))
  · obtain ⟨W⟩ := hCyclic
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.map (groupEquiv e A)⟩)))
  · obtain ⟨W⟩ := hPrime
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨W.map (groupEquiv e A)⟩))))
  · obtain ⟨W⟩ := hNine
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨W.map (groupEquiv e A) e (point_equivariant e A)⟩))))

end TernaryHighEarlierOwner

namespace OriginalMinimalBlock

variable {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    {ω₀ : Ω} (D : OriginalMinimalBlock (A := A) ω₀)

/-- Every fibre of the selected transitive block system has the same finite
cardinality as its base fibre. -/
theorem originalBlockFibre_card_eq
    (x : D.Points) :
    Nat.card (originalBlockFibre D.map x) = Nat.card D.Fibre := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq A D.base x
  calc
    Nat.card (originalBlockFibre D.map x) =
        Nat.card (originalBlockFibre D.map (a • D.base)) := by rw [ha]
    _ = Nat.card D.Fibre :=
      (Nat.card_congr
        (OriginalBlockSignCoordinates.fibreTransport D.map D.map_equivariant
          a D.base)).symm

/-- The two saturated degree-twelve orientations install their intrinsic
earlier owners, with the original normal subgroup and actual minimal block
system retained. -/
theorem degreeTwelve_high_structuralOwner
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (N : Subgroup A) [N.Normal]
    (hDegree : Nat.card Ω = 12)
    (hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)) :
    IsC1TernaryPrimeBaseOwner A ∨ IsC1BinaryNineTopOwner A Ω := by
  obtain ⟨ω₀, D, c, horient, hc, hTopRank, hRank⟩ :=
    degreeTwelve_high_top_geometry
      hChief hWeight hPrimitive h18 N hDegree hHigh
  letI : Fintype D.Points := Fintype.ofFinite D.Points
  letI : ∀ x : D.Points, Fintype (originalBlockFibre D.map x) :=
    fun x => Fintype.ofFinite (originalBlockFibre D.map x)
  rcases horient with h34 | h43
  · exact Or.inl
      (D.degreeTwelve_primeBase_owner N h34.1 h34.2.2 hRank hTopRank)
  · have hCard : ∀ x : D.Points,
        Nat.card (originalBlockFibre D.map x) = 4 := by
      intro x
      rw [D.originalBlockFibre_card_eq x, h43.1]
    let e : ∀ x : D.Points, Fin 4 ≃ originalBlockFibre D.map x :=
      fun x => (Finite.equivFinOfCardEq (hCard x)).symm
    exact Or.inr
      (D.fourByThree_nineTopOwner N c h43.2.1 h43.2.2 hc
        hTopRank hRank e)

end OriginalMinimalBlock

/-- Under the four named global ternary inputs, every normal residual pair
is accepted by an earlier structural owner or satisfies the exact `3/20`
capacity inequality. -/
theorem ternaryHigh_earlierOwner_or_capacity
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {A Ω : Type} [Group A] [Finite A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPretransitive A Ω]
    (N : Subgroup A) [N.Normal] :
    TernaryHighEarlierOwner A Ω ∨
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ≤
        3 * Nat.card Ω := by
  by_cases hHigh : 3 * Nat.card Ω <
      20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N)
  · left
    rcases ternaryHigh_action_owned_menu
        hChief hWeight hPrimitive h18 N hHigh with hThree | hA4 | hSix | hTwelve
    · exact Or.inl hThree
    · exact Or.inr (Or.inl hA4)
    · rcases degreeSix_high_structuralOwner
          hPrimitive N hSix hHigh with hOdd | hCyclic
      · exact Or.inr (Or.inr (Or.inl hOdd))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hCyclic)))
    · rcases OriginalMinimalBlock.degreeTwelve_high_structuralOwner
          hChief hWeight hPrimitive h18 N hTwelve hHigh with hPrime | hNine
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hPrime))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hNine))))
  · right
    omega

/-- Every high trivial-axis C3 state exposes a literal original orbit pair
accepted by one of the structural earlier owners.  This retains the complete
physical complement subgroup and makes no owner-counting assertion. -/
theorem c3TrivialHigh_enters_ternaryEarlierOwner
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
        TernaryHighEarlierOwner
          (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o)
          o.orbit := by
  let Owner := fun
      (o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H))
      (_N : Subgroup
        (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
      (_hN : _N.Normal) =>
        TernaryHighEarlierOwner
          (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o)
          o.orbit
  apply c3TrivialHigh_enters_orbitPairOwner b P H Owner
  · intro o N hN
    let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
    letI : MulAction.IsPretransitive A o.orbit :=
      orbitImage_pretransitive (C3ComplementSource b H) o
    letI : N.Normal := hN
    exact ternaryHigh_earlierOwner_or_capacity
      hChief hWeight hPrimitive h18 N
  · exact hH

end SymmetricSubgroupAsymptotics

end
