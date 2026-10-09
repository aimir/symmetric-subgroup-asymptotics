import SymmetricSubgroupAsymptotics.DegreeSixOwnerInducedHead
import SymmetricSubgroupAsymptotics.RepresentationCoinvariantHead
import SymmetricSubgroupAsymptotics.RepresentationElementHead

/-!
# Odd-normalizer bounds for every actual subrepresentation

Let an odd subgroup `A` act on a binary representation and let `g`
normalize `A`.  Restriction of invariant forms to `A`-fixed vectors is
injective by coprime averaging.  Applying the one-element annihilator bound
to `g` then bounds the coinvariant head of every actual subrepresentation by
the simultaneous `A`- and `g`-fixed space of the ambient representation.

This is the reusable algebraic importer for the degree-sixteen affine frame
certificates.  It removes the need to enumerate invariant submodules of the
32-dimensional induced frame.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

variable {k G V : Type} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- A form invariant under the full group is, by the same underlying map,
invariant under every subgroup. -/
def representationHeadRestrictSubgroup
    (ρ : Representation k G V) (H : Subgroup G) :
    Representation.IntertwiningMap ρ (Representation.trivial k G k) →ₗ[k]
      Representation.IntertwiningMap (ρ.comp H.subtype)
        (Representation.trivial k H k) where
  toFun f := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := by
      simpa using f.isIntertwining' h.1 }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem representationHeadRestrictSubgroup_injective
    (ρ : Representation k G V) (H : Subgroup G) :
    Function.Injective (representationHeadRestrictSubgroup ρ H) := by
  intro f g h
  apply Representation.IntertwiningMap.ext
  simpa only [representationHeadRestrictSubgroup] using
    congrArg Representation.IntertwiningMap.toLinearMap h

/-- The simultaneous fixed space displayed by an odd-normalizer witness. -/
def oddNormalizerFixedSpace
    (ρ : Representation k G V) (A : Subgroup G) (g : G) :
    Submodule k V :=
  Representation.invariants (ρ.comp A.subtype) ⊓
    representationElementFixedSpace ρ g

variable {ρ : Representation k G V} {A : Subgroup G} {g : G}

/-- The fixed space obtained after restricting an actual subrepresentation
to the normalizer embeds in the ambient simultaneous fixed space. -/
def oddNormalizerFixedEmbedding
    (hg : g ∈ Subgroup.normalizer (A : Set G))
    (B : Subrepresentation ρ) :
    representationElementFixedSpace
        (Representation.toInvariants
          (B.toRepresentation.comp
            (Subgroup.normalizer (A : Set G)).subtype)
          (A.subgroupOf (Subgroup.normalizer (A : Set G))))
        (⟨g, hg⟩ : Subgroup.normalizer (A : Set G)) →ₗ[k]
      oddNormalizerFixedSpace ρ A g where
  toFun x := ⟨x.1.1.1, by
    constructor
    · intro a
      let aN : A.subgroupOf (Subgroup.normalizer (A : Set G)) :=
        (Subgroup.subgroupOfEquivOfLe A.le_normalizer).symm a
      have ha := x.1.2 aN
      exact congrArg (fun y : B => (y : V)) ha
    · have hx := (mem_representationElementFixedSpace _ _ _).mp x.2
      apply (mem_representationElementFixedSpace _ _ _).mpr
      exact congrArg (fun y :
        Representation.invariants
          ((B.toRepresentation.comp
            (Subgroup.normalizer (A : Set G)).subtype).comp
              (A.subgroupOf (Subgroup.normalizer (A : Set G))).subtype) =>
          ((y.1 : B) : V)) hx ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem oddNormalizerFixedEmbedding_injective
    (hg : g ∈ Subgroup.normalizer (A : Set G))
    (B : Subrepresentation ρ) :
    Function.Injective (oddNormalizerFixedEmbedding hg B) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : oddNormalizerFixedSpace ρ A g => (z : V)) h

/-- Odd-order averaging followed by the one-element annihilator bound.
The order of `g` need not be supplied here; only normalizing `A` matters
for this head inequality.  The power-of-two order remains in finite frame
records as an audit of the manuscript's chosen normalizer witness. -/
theorem subrepresentation_coinvariants_le_oddNormalizerFixedSpace
    [Finite G] [FiniteDimensional k V]
    (hA : IsUnit (Nat.card A : k))
    (hg : g ∈ Subgroup.normalizer (A : Set G))
    (B : Subrepresentation ρ) :
    Module.finrank k B.toRepresentation.Coinvariants ≤
      Module.finrank k (oddNormalizerFixedSpace ρ A g) := by
  let N : Subgroup G := Subgroup.normalizer (A : Set G)
  let AN : Subgroup N := A.subgroupOf N
  let gN : N := ⟨g, hg⟩
  let sigmaN := B.toRepresentation.comp N.subtype
  letI : AN.Normal := Subgroup.normal_in_normalizer
  letI : Fintype AN := Fintype.ofFinite AN
  have hcardAN : IsUnit (Fintype.card AN : k) := by
    rw [Fintype.card_eq_nat_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe A.le_normalizer).toEquiv]
    exact hA
  letI : Invertible (Fintype.card AN : k) := hcardAN.invertible
  calc
    Module.finrank k B.toRepresentation.Coinvariants =
        Module.finrank k
          (B.toRepresentation.IntertwiningMap
            (Representation.trivial k G k)) :=
      (representationHead_finrank_eq_coinvariants B.toRepresentation).symm
    _ ≤ Module.finrank k
          (Representation.IntertwiningMap sigmaN
            (Representation.trivial k N k)) :=
      LinearMap.finrank_le_finrank_of_injective
        (f := representationHeadRestrictSubgroup B.toRepresentation N)
        (representationHeadRestrictSubgroup_injective
          B.toRepresentation N)
    _ ≤ Module.finrank k
          ((Representation.toInvariants sigmaN AN).IntertwiningMap
            (Representation.trivial k N k)) :=
      representationHead_le_normalInvariants sigmaN AN
    _ ≤ Module.finrank k
          (representationElementFixedSpace
            (Representation.toInvariants sigmaN AN) gN) :=
      representationHead_le_elementFixedSpace
        (Representation.toInvariants sigmaN AN) gN
    _ ≤ Module.finrank k (oddNormalizerFixedSpace ρ A g) :=
      (oddNormalizerFixedEmbedding hg B).finrank_le_finrank_of_injective
        (oddNormalizerFixedEmbedding_injective hg B)

/-- Binary specialization used by the finite-frame importer. -/
theorem binary_subrepresentation_coinvariants_le_oddNormalizerFixedSpace
    {G V : Type} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (A : Subgroup G) (hodd : ¬ 2 ∣ Nat.card A)
    (g : G) (hg : g ∈ Subgroup.normalizer (A : Set G))
    (B : Subrepresentation ρ) :
    Module.finrank (ZMod 2) B.toRepresentation.Coinvariants ≤
      Module.finrank (ZMod 2) (oddNormalizerFixedSpace ρ A g) := by
  apply subrepresentation_coinvariants_le_oddNormalizerFixedSpace
    (ρ := ρ) (A := A) (g := g) ?_ hg B
  exact isUnit_iff_ne_zero.mpr
    ((ZMod.natCast_eq_zero_iff (Nat.card A) 2).not.mpr hodd)

end SymmetricSubgroupAsymptotics

end
