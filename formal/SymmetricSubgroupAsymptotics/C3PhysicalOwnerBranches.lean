import SymmetricSubgroupAsymptotics.C3PhysicalStructuralOwner

/-!
# Branching the complete high-C3 physical owner

The finite high-action theorem has four structurally different outcomes.
They are retained as separate relabelling-invariant predicates of the
complete physical subgroup, so later counting estimates can be attached to
the first applicable branch without duplicate ownership.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

inductive C3PhysicalOwnerKind
  | ternaryPGroup
  | naturalA4
  | degreeSix
  | degreeTwelve
  deriving DecidableEq, Fintype

def C3PhysicalOwnerKind.property
    (k : C3PhysicalOwnerKind) (A Ω : Type) [Group A] [MulAction A Ω] : Prop :=
  match k with
  | .ternaryPGroup => IsPGroup 3 A
  | .naturalA4 => IsNaturalA4Action A Ω
  | .degreeSix => Nat.card Ω = 6
  | .degreeTwelve => Nat.card Ω = 12

/-- One classified branch of the complete high-C3 physical owner.  The
normal pair, strict high inequality and intrinsic structural owner remain
part of the witness. -/
def C3PhysicalStructuralOwnerBranch (k : C3PhysicalOwnerKind) (n : ℕ)
    (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∃ (b : ℕ)
    (e : TernaryCyclic ⊕ Fin b ≃ Fin n)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b))),
      relabelSubgroup e (H.map (fusionOrbitAction ternaryRegularAction)) = G ∧
      ∃ o : OrbitProfileFromOrbits.Orbit (C3ComplementSource b H),
        ∃ (N : Subgroup
            (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o))
          (hN : N.Normal),
          letI := hN
          3 * Nat.card o.orbit <
              20 * Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) ∧
            TernaryHighEarlierOwner
              (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o)
              o.orbit ∧
            k.property
              (OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o)
              o.orbit

theorem c3PhysicalStructuralOwnerBranch_owner
    {k : C3PhysicalOwnerKind} {n : ℕ}
    {G : Subgroup (Equiv.Perm (Fin n))}
    (h : C3PhysicalStructuralOwnerBranch k n G) :
    C3PhysicalStructuralOwner n G := by
  rcases h with ⟨b, e, H, hG, o, N, hN, hHigh, hOwner, _⟩
  exact ⟨b, e, H, hG, o, N, hN, hHigh, hOwner⟩

theorem c3PhysicalStructuralOwnerBranch_relabel_iff
    (k : C3PhysicalOwnerKind) {m n : ℕ}
    (hmn : m = n) (e : Fin m ≃ Fin n)
    (G : Subgroup (Equiv.Perm (Fin m))) :
    C3PhysicalStructuralOwnerBranch k n (relabelSubgroup e G) ↔
      C3PhysicalStructuralOwnerBranch k m G := by
  subst n
  constructor
  · rintro ⟨b, c, H, hc, o, N, hN, hHigh, hOwner, hk⟩
    refine ⟨b, c.trans e.symm, H, ?_, o, N, hN, hHigh, hOwner, hk⟩
    calc
      relabelSubgroup (c.trans e.symm)
          (H.map (fusionOrbitAction ternaryRegularAction)) =
        relabelSubgroup e.symm
          (relabelSubgroup c
            (H.map (fusionOrbitAction ternaryRegularAction))) := by
              rw [relabelSubgroup_trans]
      _ = relabelSubgroup e.symm (relabelSubgroup e G) := by rw [hc]
      _ = G := relabelSubgroup_symm e G
  · rintro ⟨b, c, H, hc, o, N, hN, hHigh, hOwner, hk⟩
    refine ⟨b, c.trans e, H, ?_, o, N, hN, hHigh, hOwner, hk⟩
    calc
      relabelSubgroup (c.trans e)
          (H.map (fusionOrbitAction ternaryRegularAction)) =
        relabelSubgroup e
          (relabelSubgroup c
            (H.map (fusionOrbitAction ternaryRegularAction))) := by
              rw [relabelSubgroup_trans]
      _ = relabelSubgroup e G := by rw [hc]

/-- The strict high inequality classifies every complete physical owner into
one of the four action branches. -/
theorem c3PhysicalStructuralOwner_branch_cover
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : C3PhysicalStructuralOwner n G) :
    ∃ k, C3PhysicalStructuralOwnerBranch k n G := by
  rcases hG with ⟨b, e, H, hphysical, o, N, hN, hHigh, hOwner⟩
  let A := OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) o
  letI : MulAction.IsPretransitive A o.orbit :=
    orbitImage_pretransitive (C3ComplementSource b H) o
  letI : N.Normal := hN
  rcases ternaryHigh_action_owned_menu hChief hWeight hPrimitive h18
      (A := A) (Ω := o.orbit) N hHigh with hThree | hA4 | hSix | hTwelve
  · exact ⟨.ternaryPGroup,
      b, e, H, hphysical, o, N, hN, hHigh, hOwner, hThree⟩
  · exact ⟨.naturalA4,
      b, e, H, hphysical, o, N, hN, hHigh, hOwner, hA4⟩
  · exact ⟨.degreeSix,
      b, e, H, hphysical, o, N, hN, hHigh, hOwner, hSix⟩
  · exact ⟨.degreeTwelve,
      b, e, H, hphysical, o, N, hN, hHigh, hOwner, hTwelve⟩

def c3PhysicalOwnerKindEquiv : Fin 4 ≃ C3PhysicalOwnerKind :=
  (Fintype.equivFin C3PhysicalOwnerKind).symm

def c3PhysicalStructuralBranchMenu
    (n : ℕ) (i : Fin 4) (G : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  C3PhysicalStructuralOwnerBranch (c3PhysicalOwnerKindEquiv i) n G

theorem c3PhysicalStructuralBranchMenu_natural :
    DegreeNaturalOwnerMenu c3PhysicalStructuralBranchMenu := by
  intro m n hmn e i G
  exact c3PhysicalStructuralOwnerBranch_relabel_iff
    (c3PhysicalOwnerKindEquiv i) hmn e G

theorem c3PhysicalStructuralBranchMenu_cover
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} {G : Subgroup (Equiv.Perm (Fin n))}
    (hG : C3PhysicalStructuralOwner n G) :
    ∃ i, c3PhysicalStructuralBranchMenu n i G := by
  obtain ⟨k, hk⟩ := c3PhysicalStructuralOwner_branch_cover
    hChief hWeight hPrimitive h18 hG
  exact ⟨c3PhysicalOwnerKindEquiv.symm k, by
    simpa only [c3PhysicalStructuralBranchMenu,
      Equiv.apply_symm_apply] using hk⟩

theorem c3TrivialHigh_enters_physicalStructuralBranchMenu
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hPrimitive : PrimitiveTernaryStrictHeadBound)
    (h18 : DegreeEighteenTernaryHeadBound)
    (b n : ℕ)
    (e : TernaryCyclic ⊕ Fin b ≃ Fin n)
    (P : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)) → Prop)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (hH : C3TrivialHighPredicate b P H) :
    ∃ i, c3PhysicalStructuralBranchMenu n i
      (relabelSubgroup e
        (H.map (fusionOrbitAction ternaryRegularAction))) := by
  apply c3PhysicalStructuralBranchMenu_cover
    hChief hWeight hPrimitive h18
  exact c3TrivialHigh_enters_physicalStructuralOwner
    hChief hWeight hPrimitive h18 b n e P H hH

end SymmetricSubgroupAsymptotics

end
