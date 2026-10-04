import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate

/-!
# Zmud's faithful-character theorem

For a finite group, Zmud proved that the least number of irreducible
constituents in a faithful complex representation is the least number of
normal generators of the socle.  We expose exactly that published theorem,
at its group-theoretic boundary, and derive the character-certificate object
used by the pre-`E7` counting argument.

The modern reference is Benjamin Steinberg, *Extensions of Theorems of
Gaschutz, Zmud and Rhodes on Faithful Representations*, Algebras and
Representation Theory 26 (2023), 1641--1667, DOI
`10.1007/s10468-022-10149-y`; see the group case of the Zmud theorem
(arXiv:2201.09129).  The input below is a literature theorem about arbitrary
finite groups.  It does not mention affine blocks, counting envelopes, or any
project owner.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A nontrivial minimal normal subgroup. -/
def IsMinimalNormalSubgroup {G : Type} [Group G]
    (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧
    ∀ M : Subgroup G, M.Normal → M ≠ ⊥ → M ≤ N → M = N

/-- The socle as the supremum of the literal minimal normal subgroups. -/
def finiteGroupSocle (G : Type) [Group G] : Subgroup G :=
  sSup {N : Subgroup G | IsMinimalNormalSubgroup N}

/-- The socle is generated, as a normal subgroup, by at most `t` elements.
Padding by identity elements makes this an exact `Fin t`-indexed statement. -/
def SocleNormalGeneratorBound (G : Type) [Group G] (t : ℕ) : Prop :=
  ∃ x : Fin t → G,
    Subgroup.normalClosure (Set.range x) = finiteGroupSocle G

/-- Zmud's theorem in the only direction used here: `t` normal generators
of the socle give `t` jointly faithful irreducible complex representations.
The theorem is an explicit published input, never a project-owned axiom. -/
def ZmudFaithfulCharacterTupleInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t : ℕ),
    SocleNormalGeneratorBound G t →
      ∃ rho : Fin t → FiniteIrreducibleRepresentation ℂ G,
        ∀ g : G, (∀ i, (rho i).action g = 1) → g = 1

namespace ZmudFaithfulCharacterTupleInput

/-- Convert the published tuple into the project's general-character slot
format.  No binary-primary or extra linear positions are introduced. -/
noncomputable def generalTuple
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (hgen : SocleNormalGeneratorBound G t) : CharacterSlotTuple G := by
  let rho := Classical.choose (hZmud G t hgen)
  have hrho := Classical.choose_spec (hZmud G t hgen)
  exact
    { binaryCount := 0
      linearCount := 0
      generalCount := t
      binary := Fin.elim0
      binary_twoGroup := fun i => Fin.elim0 i
      linear := Fin.elim0
      general := rho
      faithful := by
        intro g _ _ hg
        exact hrho g hg }

/-- The corresponding mixed quotient certificate. -/
noncomputable def generalCertificate
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (hgen : SocleNormalGeneratorBound G t) :
    CharacterQuotientCertificate G where
  mode := .mixed
  tuple := hZmud.generalTuple hgen
  prime := 2
  known := by
    intro h
    cases h

@[simp] theorem generalTuple_binaryCount
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (hgen : SocleNormalGeneratorBound G t) :
    (hZmud.generalTuple hgen).binaryCount = 0 := rfl

@[simp] theorem generalTuple_linearCount
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (hgen : SocleNormalGeneratorBound G t) :
    (hZmud.generalTuple hgen).linearCount = 0 := rfl

@[simp] theorem generalTuple_generalCount
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (hgen : SocleNormalGeneratorBound G t) :
    (hZmud.generalTuple hgen).generalCount = t := rfl

@[simp] theorem generalCertificate_slope
    (hZmud : ZmudFaithfulCharacterTupleInput)
    {G : Type} [Group G] [Finite G] {t : ℕ}
    (hgen : SocleNormalGeneratorBound G t) :
    (hZmud.generalCertificate hgen).slope =
      (t : ℝ) * (Real.logb 2 5 / 3) := by
  simp only [generalCertificate, CharacterQuotientCertificate.slope,
    generalTuple_binaryCount, generalTuple_linearCount,
    generalTuple_generalCount, CharacterQuotientMode.generalSlope,
    Nat.cast_zero, zero_mul, zero_add]

end ZmudFaithfulCharacterTupleInput
end SymmetricSubgroupAsymptotics

end
