import SymmetricSubgroupAsymptotics.TernaryNormalizerOrbitPrefix

/-!
# Binary quotient rank through actual ternary centralizer orbits

The orbit action of a ternary centralizer has kernel of exponent three.
Consequently every binary quotient of any actual subgroup of that
centralizer factors through its permutation image on the original orbits.
The permutation prime-rank theorem bounds its binary character rank by
half the number of orbits. No faithful point action on the quotient is
postulated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace TernaryCentralizerOrbitRank

open TernaryNormalizerOrbitPrefix

/-- A binary quotient of a subgroup of the actual ternary centralizer is
controlled by the original orbit action, with the same quotient map. -/
theorem binary_quotient_rank_le
    {G X A : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Group A] [Finite A]
    (H L : Subgroup G) (hH : ∀ h : H, h ^ 3 = 1)
    (hL : L ≤ Subgroup.centralizer (H : Set G))
    (pi : L →* A) (hpi : Function.Surjective pi) (hA : IsPGroup 2 A) :
    binaryCharacterRank A ≤ Nat.card (Orbits (X := X) H) / 2 := by
  let toNormalizer : L →* Subgroup.normalizer (H : Set G) :=
    Subgroup.inclusion (hL.trans (Subgroup.centralizer_le_normalizer _))
  let phi : L →* Equiv.Perm (Orbits (X := X) H) :=
    (orbitPermHom H).comp toNormalizer
  have hker : phi.ker ≤ pi.ker := by
    intro x hx
    have hconj : H.normalizerMonoidHom (toNormalizer x) = 1 := by
      change toNormalizer x ∈ H.normalizerMonoidHom.ker
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hL x.property
    have hjoint : toNormalizer x ∈ (jointAction (X := X) H).ker := by
      apply Prod.ext
      · exact hconj
      · exact hx
    have hx3 : x ^ 3 = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : Subgroup.normalizer (H : Set G) ↦ (z : G))
        (jointAction_kernel_cube H hH (toNormalizer x) hjoint)
    change pi x = 1
    apply (hA.powEquiv (by decide : Nat.Coprime 2 3)).injective
    change pi x ^ 3 = 1 ^ 3
    rw [← map_pow, hx3, map_one, one_pow]
  have hker' : phi.rangeRestrict.ker ≤ pi.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  let q : phi.range →* A :=
    phi.rangeRestrict.liftOfSurjective phi.rangeRestrict_surjective ⟨pi, hker'⟩
  have hq_apply (x : L) : q (phi.rangeRestrict x) = pi x :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx⟩ := hpi a
    exact ⟨phi.rangeRestrict x, (hq_apply x).trans hx⟩
  have hrank := (primeCharacterInflation 2 q).finrank_le_finrank_of_injective
    (primeCharacterInflation_injective 2 q hq)
  exact hrank.trans (permutation_primeCharacterRank_le 2 phi.range (Orbits (X := X) H))

/-- If the original centralizer contains lifts of every element of an
embedded binary subgroup, that subgroup has the same orbit-rank bound.
Only its actual preimage is used; no action on the quotient is assumed. -/
theorem binary_subgroup_rank_le_of_lifts
    {G X Q A : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Group Q]
    [Group A] [Finite A]
    (H : Subgroup G) (hH : ∀ h : H, h ^ 3 = 1)
    (pi : G →* Q) (e : A →* Q) (he : Function.Injective e)
    (hA : IsPGroup 2 A)
    (hlift : ∀ a : A, ∃ g : Subgroup.centralizer (H : Set G), pi g = e a) :
    binaryCharacterRank A ≤ Nat.card (Orbits (X := X) H) / 2 := by
  let L : Subgroup G := e.range.comap pi ⊓ Subgroup.centralizer (H : Set G)
  let f : L →* e.range := (pi.comp L.subtype).codRestrict e.range
    (fun x ↦ x.property.1)
  let equiv : A ≃* e.range := MonoidHom.ofInjective he
  let q : L →* A := equiv.symm.toMonoidHom.comp f
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨g, hg⟩ := hlift a
    let x : L := ⟨g, ⟨⟨a, hg.symm⟩, g.property⟩⟩
    refine ⟨x, ?_⟩
    apply equiv.injective
    change equiv (equiv.symm (f x)) = equiv a
    rw [equiv.apply_symm_apply]
    exact Subtype.ext hg
  exact binary_quotient_rank_le H L hH inf_le_right q hq hA

/-- Lifts of all central involutions suffice for the central binary rank.
The cardinality of the original orbit space is the only numerical input. -/
theorem central_finrank_le_of_lifts
    {G X Q : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [Group Q] [Finite Q]
    (H : Subgroup G) (hH : ∀ h : H, h ^ 3 = 1)
    (pi : G →* Q)
    (hlift : ∀ z : binaryCentralOmega Q,
      ∃ g : Subgroup.centralizer (H : Set G),
        pi g = binaryCentralOmegaEmbedding z) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)) ≤
      Nat.card (Orbits (X := X) H) / 2 := by
  let A := Multiplicative (Additive (binaryCentralOmega Q))
  let e : A →* Q := {
    toFun z := binaryCentralOmegaEmbedding z.toAdd.toMul
    map_one' := map_one binaryCentralOmegaEmbedding
    map_mul' z w := map_mul binaryCentralOmegaEmbedding _ _ }
  have he : Function.Injective e :=
    binaryCentralOmegaEmbedding_injective.comp
      (Additive.toMul.injective.comp Multiplicative.toAdd.injective)
  have hA : IsPGroup 2 A := by
    intro z
    refine ⟨1, ?_⟩
    apply he
    change binaryCentralOmegaEmbedding z.toAdd.toMul ^ 2 = 1
    exact congrArg Subtype.val z.toAdd.toMul.property
  have hb := binary_subgroup_rank_le_of_lifts (X := X) H hH pi e he hA
    (fun z ↦ hlift z.toAdd.toMul)
  rwa [binaryCharacterRank_multiplicative] at hb

end TernaryCentralizerOrbitRank
end SymmetricSubgroupAsymptotics

end
