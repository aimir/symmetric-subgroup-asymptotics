import SymmetricSubgroupAsymptotics.Non2PreE7SmallOrderSemisimple
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing

/-!
# Normal generators in permutation sections

The published permutation-subgroup generator bound passes to every section
of a literal permutation group.  Consequently, any ambient normal subgroup
which embeds in such a section costs at most the original permutation
degree in normal generators.

This is the form needed by the affine block arguments.  The subgroup being
bounded need not itself be a permutation subgroup: it may be a selected sum
of ambient minimal normal subgroups inside a quotient.  Its faithful map into
the literal top section is retained explicitly.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace MarkedC4

/-- Ordinary generator number does not increase under a surjective
homomorphism. -/
theorem genRank_le_of_surjective
    {A B : Type} [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Surjective f) :
    genRank B ≤ genRank A := by
  obtain ⟨S, hScard, hS⟩ := genRank_spec (G := A)
  let T : Finset B := S.image f
  have hT : Subgroup.closure (T : Set B) = ⊤ := by
    have hmap := congrArg (Subgroup.map f) hS
    simpa only [T, Finset.coe_image, MonoidHom.map_closure,
      Subgroup.map_top_of_surjective f hf] using hmap
  calc
    genRank B ≤ T.card := genRank_le hT
    _ ≤ S.card := Finset.card_image_le
    _ = genRank A := hScard

/-- A generating set also normally generates the whole group. -/
theorem normalGen_top_le_genRank
    (G : Type) [Group G] [Finite G] :
    normalGen (⊤ : Subgroup G) ≤ genRank G := by
  obtain ⟨S, hScard, hS⟩ := genRank_spec (G := G)
  rw [← hScard]
  apply normalGen_le (s := S) (by simp)
  apply le_antisymm
  · exact le_top
  · rw [← hS]
    exact Subgroup.closure_le_normalClosure

end MarkedC4

/-- A selected ambient normal subgroup which embeds in a quotient section
of a literal degree-`s` permutation group needs at most `s` ambient normal
generators.

The preimage in `R` of the embedded range is an actual subgroup of
`S_s`, so the published Holt--Roney-Dougal bound applies to that preimage.
Its generating set descends through `q`, is transported back through the
faithful map `f`, and then normally generates `K` in the original ambient
group. -/
theorem normalGen_normalSubgroup_le_degree_of_permutationSection
    (hgen : PermutationSubgroupGeneratorBound)
    {s : ℕ}
    (R : Subgroup (Equiv.Perm (Fin s)))
    {A : Type} [Group A] [Finite A]
    (q : R →* A) (hq : Function.Surjective q)
    {G : Type} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal]
    (f : K →* A) (hf : Function.Injective f)
    (hs : 2 ≤ s) :
    MarkedC4.normalGen K ≤ s := by
  let H : Subgroup A := f.range
  let J : Subgroup R := H.comap q
  let qJ : J →* H :=
    (q.comp J.subtype).codRestrict H (fun x => x.2)
  have hqJ : Function.Surjective qJ := by
    intro y
    obtain ⟨x, hx⟩ := hq y.1
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    show q x ∈ H
    rw [hx]
    exact y.2
  let jinc : J →* Equiv.Perm (Fin s) := R.subtype.comp J.subtype
  have hjinc : Function.Injective jinc := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  have hjrange : Function.Injective jinc.rangeRestrict :=
    MonoidHom.rangeRestrict_injective_iff.mpr hjinc
  let eJ : J ≃* jinc.range := MulEquiv.ofBijective jinc.rangeRestrict
    ⟨hjrange, jinc.rangeRestrict_surjective⟩
  obtain ⟨S, hS, hScard⟩ := hgen s jinc.range
  let e : K ≃* H := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun x y h => hf (congrArg Subtype.val h),
      f.rangeRestrict_surjective⟩
  have hgenH : MarkedC4.genRank H ≤ S.card := by
    exact (MarkedC4.genRank_le_of_surjective qJ hqJ).trans
      ((MarkedC4.genRank_le_of_surjective eJ.symm.toMonoidHom
        eJ.symm.surjective).trans (MarkedC4.genRank_le hS))
  have hgenK : MarkedC4.genRank K ≤ S.card := by
    exact (MarkedC4.genRank_le_of_surjective e.symm.toMonoidHom
      e.symm.surjective).trans hgenH
  calc
    MarkedC4.normalGen K ≤
        MarkedC4.normalGen (⊤ : Subgroup K) :=
      MarkedC4.normalGen_normalSubgroup_le_internal K
    _ ≤ MarkedC4.genRank K := MarkedC4.normalGen_top_le_genRank K
    _ ≤ S.card := hgenK
    _ ≤ s := by omega

end SymmetricSubgroupAsymptotics

end
