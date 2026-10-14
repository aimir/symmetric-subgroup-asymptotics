import SymmetricSubgroupAsymptotics.BinaryAbelianTopPrefixBranch
import SymmetricSubgroupAsymptotics.BinaryCharacterProducts
import SymmetricSubgroupAsymptotics.PrimeSectionalCharacterRank
import SymmetricSubgroupAsymptotics.PermutationPrimeGroupRank

/-!
# Binary prefixes from an actual normalizer image

Suppose an actual group mapping onto `Q` embeds jointly into a commutative
group of order at most two and permutations of `X`. Its sectional binary
rank is at most `1 + |X| / 2`; its derived subgroup embeds in the second
factor alone and has sectional binary rank at most `|X| / 2`.

These two bounds pass through the original quotient map to the central
binary omega and its intersection with the derived subgroup. For eight
orbit points and a binary target, the checked full-order character bridge
then constructs the designated prefix and four relative orbit slots.
No permutation action on the quotient itself is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative

namespace SymmetricSubgroupAsymptotics.BinaryNormalizerImagePrefix

private theorem sectional_surjection
    {F Q : Type} [Group F] [Finite F] [Group Q] {r : ℕ}
    (hF : PrimeSectionalRankBound 2 F r)
    (pi : F →* Q) (hpi : Function.Surjective pi) :
    PrimeSectionalRankBound 2 Q r := by
  intro L
  exact PrimeSectionalRankBound.quotient_rank_le 2 hF (L.comap pi)
    (pi.subgroupComap L) (pi.subgroupComap_surjective_of_surjective L hpi)

private theorem vector_finrank_le_of_embedding
    {Q V : Type} [Group Q] [Finite Q] [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {r : ℕ}
    (hQ : PrimeSectionalRankBound 2 Q r)
    (f : Multiplicative V →* Q) (hf : Function.Injective f) :
    Module.finrank (ZMod 2) V ≤ r := by
  have h := primeCharacterRank_le_of_injective 2 hQ f hf
  change binaryCharacterRank (Multiplicative V) ≤ r at h
  rwa [binaryCharacterRank_multiplicative] at h

theorem central_finrank_le_of_sectional
    {Q : Type} [Group Q] [Finite Q] {r : ℕ}
    (hQ : PrimeSectionalRankBound 2 Q r) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ r := by
  let f : Multiplicative (Additive (binaryCentralOmega Q)) →* Q := {
    toFun := fun z ↦ binaryCentralOmegaEmbedding z.toAdd.toMul
    map_one' := map_one binaryCentralOmegaEmbedding
    map_mul' := fun z w ↦ map_mul binaryCentralOmegaEmbedding _ _ }
  exact vector_finrank_le_of_embedding hQ f
    (binaryCentralOmegaEmbedding_injective.comp
      (Additive.toMul.injective.comp Multiplicative.toAdd.injective))

theorem derivedCentral_finrank_le_of_sectional
    {Q : Type} [Group Q] [Finite Q] {r : ℕ}
    (hD : PrimeSectionalRankBound 2 (commutator Q) r) :
    Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule (commutator Q)) ≤ r := by
  let f : Multiplicative (binaryCentralOmegaSubmodule (commutator Q)) →*
      commutator Q := {
    toFun := fun z ↦ ⟨binaryCentralOmegaEmbedding z.toAdd.val.toMul,
      z.toAdd.property⟩
    map_one' := by apply Subtype.ext; exact map_one binaryCentralOmegaEmbedding
    map_mul' := by intro z w; apply Subtype.ext; exact map_mul binaryCentralOmegaEmbedding _ _ }
  apply vector_finrank_le_of_embedding hD f
  intro z w h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply Additive.toMul.injective
  exact binaryCentralOmegaEmbedding_injective
    (congrArg (fun x : commutator Q ↦ (x : Q)) h)

private theorem derived_map_eq
    {F Q : Type} [Group F] [Group Q]
    (pi : F →* Q) (hpi : Function.Surjective pi) :
    (commutator F).map pi = commutator Q := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ hpi]

/-- The original quotient map restricts onto the actual derived subgroup. -/
def derivedMap {F Q : Type} [Group F] [Group Q]
    (pi : F →* Q) (hpi : Function.Surjective pi) :
    commutator F →* commutator Q :=
  (pi.comp (commutator F).subtype).codRestrict (commutator Q) (by
    intro x
    have h : pi x ∈ (commutator F).map pi := ⟨x, x.property, rfl⟩
    rwa [derived_map_eq pi hpi] at h)

theorem derivedMap_surjective {F Q : Type} [Group F] [Group Q]
    (pi : F →* Q) (hpi : Function.Surjective pi) :
    Function.Surjective (derivedMap pi hpi) := by
  intro q
  have h : q.val ∈ (commutator F).map pi := by
    rw [derived_map_eq pi hpi]
    exact q.property
  obtain ⟨x, hx, he⟩ := h
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- Joint faithfulness retains correlations between the automorphism and
orbit factors. Only the derived source is restricted to the orbit factor. -/
theorem central_and_derived_finrank_le
    {F Q C X : Type} [Group F] [Finite F] [Group Q] [Finite Q]
    [Group C] [Finite C] [IsMulCommutative C] [Finite X]
    (alpha : F →* C) (beta : F →* Equiv.Perm X)
    (hfaithful : Function.Injective (alpha.prod beta))
    (hC : Nat.card C ≤ 2) (pi : F →* Q) (hpi : Function.Surjective pi) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤ 1 + Nat.card X / 2 ∧
      Module.finrank (ZMod 2) (binaryCentralOmegaSubmodule (commutator Q)) ≤
        Nat.card X / 2 := by
  have hCsection : PrimeSectionalRankBound 2 C 1 :=
    primeSectionalRankBound_of_card_le 2 C 1 (by simpa using hC)
  have hXsection : PrimeSectionalRankBound 2 (Equiv.Perm X) (Nat.card X / 2) := by
    intro L
    exact permutation_primeCharacterRank_le 2 L X
  have hFsection : PrimeSectionalRankBound 2 F (1 + Nat.card X / 2) :=
    PrimeSectionalRankBound.of_injective 2
      (PrimeSectionalRankBound.prod 2 hCsection hXsection)
      (alpha.prod beta) hfaithful
  have hderivedFaithful : Function.Injective (beta.comp (commutator F).subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply hfaithful
    apply Prod.ext
    · exact (Abelianization.commutator_subset_ker alpha x.property).trans
        (Abelianization.commutator_subset_ker alpha y.property).symm
    · exact hxy
  have hDsection : PrimeSectionalRankBound 2 (commutator F) (Nat.card X / 2) :=
    PrimeSectionalRankBound.of_injective 2 hXsection
      (beta.comp (commutator F).subtype) hderivedFaithful
  exact ⟨central_finrank_le_of_sectional (sectional_surjection hFsection pi hpi),
    derivedCentral_finrank_le_of_sectional
      (sectional_surjection hDsection (derivedMap pi hpi) (derivedMap_surjective pi hpi))⟩

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- Eight actual orbit points suffice for the binary exceptional branch. -/
theorem binaryPrefixOrbitInput_of_eight_orbit_image
    {F Q C X : Type} [Group F] [Finite F] [Group Q] [Finite Q]
    [Group C] [Finite C] [IsMulCommutative C] [Finite X]
    (alpha : F →* C) (beta : F →* Equiv.Perm X)
    (hfaithful : Function.Injective (alpha.prod beta))
    (hC : Nat.card C ≤ 2) (hX : Nat.card X = 8)
    (pi : F →* Q) (hpi : Function.Surjective pi) (hQ : IsPGroup 2 Q) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput Q
      (degreeTwoPairRelativeProfile 1 0 0 4)) := by
  obtain ⟨hc, hd⟩ := central_and_derived_finrank_le alpha beta hfaithful hC pi hpi
  rw [hX] at hc hd
  exact nonempty_binaryPrefixOrbitInput_of_ranks hQ 4 hc hd

end SymmetricSubgroupAsymptotics.BinaryNormalizerImagePrefix
