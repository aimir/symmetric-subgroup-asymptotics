import SymmetricSubgroupAsymptotics.BinaryPairParityGraph
import SymmetricSubgroupAsymptotics.BinaryPairAffineCoboundary
import SymmetricSubgroupAsymptotics.BinarySwapCocycle

/-! The original two-block action and the zero-twist conjugation.

The index-two subgroup and its two actual point orbits determine the
parity action internally. Vanishing of the original parity cocycle on
that subgroup then gives actual point conjugacy of the whole original
source to its full zero affine action. No involutory outside lift, split
source extension, or equality of a larger normal subgroup is assumed.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitSplit

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [MulAction.IsPretransitive G X] (H : Subgroup G) [H.Normal]

/-- The original set stabilizer of either orbit is the actual index-two
subgroup, not an abstract image acting on two replacement labels. -/
theorem orbit_stabilizer_eq_of_index_two
    (hindex : H.index=2) (hclasses : Nat.card (MulAction.orbitRel.Quotient H X)=2)
    (o : MulAction.orbitRel.Quotient H X) : MulAction.stabilizer G o.orbit=H := by
  have hi := normal_orbit_classes_card_eq_index H o.out
  have he : H⊔MulAction.stabilizer G o.out=H := by
    by_contra hn
    have hlt : H<H⊔MulAction.stabilizer G o.out :=
      lt_of_le_of_ne le_sup_left (Ne.symm hn)
    have hb := Subgroup.index_strictAnti hlt
    rw [← hi,hclasses,hindex] at hb
    omega
  rw [o.orbit_eq_orbit_out Quotient.out_eq']
  exact (stabilizer_normal_orbit_eq H o.out).trans he

theorem mem_preserves_orbit_of_index_two
    (hindex : H.index=2) (hclasses : Nat.card (MulAction.orbitRel.Quotient H X)=2)
    (o : MulAction.orbitRel.Quotient H X) (g : G) (hg : g∈H) : g • o.orbit=o.orbit := by
  apply MulAction.mem_stabilizer_iff.mp
  rw [orbit_stabilizer_eq_of_index_two H hindex hclasses o]
  exact hg

theorem not_mem_swaps_orbits_of_index_two
    (hindex : H.index=2) (hclasses : Nat.card (MulAction.orbitRel.Quotient H X)=2)
    (o₁ o₂ : MulAction.orbitRel.Quotient H X)
    (hcover : ∀ o : MulAction.orbitRel.Quotient H X,o=o₁ ∨ o=o₂)
    (g : G) (hg : g∉H) : g • o₁.orbit=o₂.orbit := by
  let o : MulAction.orbitRel.Quotient H X := Quotient.mk'' (g • o₁.out)
  have he : g • o₁.orbit=o.orbit := by
    rw [o₁.orbit_eq_orbit_out Quotient.out_eq',MulAction.smul_orbit_eq_orbit_smul]
    rfl
  rcases hcover o with ho | ho
  · have hs : g∈MulAction.stabilizer G o₁.orbit :=
      MulAction.mem_stabilizer_iff.mpr (he.trans (congrArg (fun q => q.orbit) ho))
    rw [orbit_stabilizer_eq_of_index_two H hindex hclasses o₁] at hs
    exact (hg hs).elim
  · exact he.trans (congrArg (fun q => q.orbit) ho)

end SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitSplit

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open PermutationBinaryTwoOrbitSplit

variable {X I : Type} {U : Subgroup (Equiv.Perm X)} [Finite I]
    (F : BinaryPairFrame U I) [MulAction.IsPretransitive F.top.range I]
    (H : Subgroup F.top.range) [H.Normal]
    (o₁ o₂ : MulAction.orbitRel.Quotient H I) (hne : o₁≠o₂)
    (hM : F.kernelSpace=twoOrbitAugmentation H o₁ o₂)
    (hindex : H.index=2) (hclasses : Nat.card (MulAction.orbitRel.Quotient H I)=2)
    (hcover : ∀ o : MulAction.orbitRel.Quotient H I,o=o₁ ∨ o=o₂)

include hindex hclasses hcover in
/-- The action in the exact original parity chart is literally identity
on H and the coordinate swap outside H. -/
theorem parityRepresentation_apply (t : F.top.range) (p : ZMod 2 × ZMod 2) :
    F.parityRepresentation H o₁ o₂ hne hM t p=
      if t∈H then p else (p.2,p.1) := by
  classical
  let E := F.parityQuotientEquiv H o₁ o₂ hne hM
  have hsurj : Function.Surjective (F.paritySum H o₁ o₂) := by
    intro b
    obtain ⟨a,ha⟩ := F.kernelSpace.mkQ_surjective (E.symm b)
    refine ⟨a,?_⟩
    rw [← F.parityQuotientEquiv_mk H o₁ o₂ hne hM]
    change E (F.kernelSpace.mkQ a)=b
    rw [ha,E.apply_symm_apply]
  obtain ⟨a,rfl⟩ := hsurj p
  rw [F.parityRepresentation_sum H o₁ o₂ hne hM t a]
  by_cases ht : t∈H
  · rw [if_pos ht]
    apply Prod.ext
    · exact (orbitSum_translate H o₁ o₁ t
        (mem_preserves_orbit_of_index_two H hindex hclasses o₁ t ht) a).symm
    · exact (orbitSum_translate H o₂ o₂ t
        (mem_preserves_orbit_of_index_two H hindex hclasses o₂ t ht) a).symm
  · rw [if_neg ht]
    apply Prod.ext
    · exact (orbitSum_translate H o₂ o₁ t
        (not_mem_swaps_orbits_of_index_two H hindex hclasses o₂ o₁
          (fun o => (hcover o).symm) t ht) a).symm
    · exact (orbitSum_translate H o₁ o₂ t
        (not_mem_swaps_orbits_of_index_two H hindex hclasses o₁ o₂ hcover t ht) a).symm

include hindex hclasses hcover in
/-- The zero restricted parity character is a genuine zero-twist branch:
it supplies an actual conjugating flip on the original points. -/
theorem exists_physical_conjugate_eq_split_of_zero_parity
    (hz : ∀ t∈H,F.parityClass H o₁ o₂ hne hM t=0) :
    ∃ a : I → ZMod 2,
      U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom=F.splitAffineAction := by
  obtain ⟨g,hg⟩ := exists_orbit_translation H o₁ o₂
  have hgnot : g∉H := by
    intro hm
    have hf := mem_preserves_orbit_of_index_two H hindex hclasses o₁ g hm
    exact hne (MulAction.orbitRel.Quotient.orbit_injective (hf.symm.trans hg))
  obtain ⟨b,hb⟩ := BinarySwapCocycle.exists_coboundary_of_zero_on_kernel H
    (F.parityRepresentation H o₁ o₂ hne hM) hindex
    (F.parityRepresentation_apply H o₁ o₂ hne hM hindex hclasses hcover)
    g hgnot (F.parityCocycle H o₁ o₂ hne hM) hz
  let E := F.parityQuotientEquiv H o₁ o₂ hne hM
  apply F.exists_physical_conjugate_eq_split_of_coboundary (E.symm b)
  intro t
  apply E.injective
  rw [map_sub,E.apply_symm_apply]
  change F.parityClass H o₁ o₂ hne hM t=
    F.parityRepresentation H o₁ o₂ hne hM t b-b
  exact hb t

end SymmetricSubgroupAsymptotics.BinaryPairFrame
