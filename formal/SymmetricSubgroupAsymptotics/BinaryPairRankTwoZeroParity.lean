import SymmetricSubgroupAsymptotics.BinaryPairRankTwoTranslationChart
import SymmetricSubgroupAsymptotics.BinaryAdditiveChartParity
import SymmetricSubgroupAsymptotics.BinarySwapCocycleFirstZero
import SymmetricSubgroupAsymptotics.BinaryPairParityAction

/-! Zero first parity gives zero full original restricted parity.

The additive chart's first block is an actual original H-orbit. It is
one of the two literal orbit subsets used by the exact affine parity
chart. Original outside conjugation exchanges the two restricted parity
coordinates; hence either zero coordinate forces the entire restricted
cocycle to vanish. The checked original-point conjugation then applies.
No normal containment or carrier identification is asserted here.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open PermutationBinaryTwoOrbitSplit

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]
    [Finite X] [Finite I] [MulAction.IsPretransitive F.top.range I]
    (hU : IsPGroup 2 U) (hI : Nat.card I=8)
    (hres : F.EightPairRankTwoResidual N)
    (hlarge : 8<Nat.card F.top.range)

/-- The zero alternative complementary to the actual nonzero-parity
character owner gives point conjugacy of the whole original source. -/
theorem rankTwo_zero_first_parity_physical_conjugate
    (hzero : ∀ h,F.rankTwoTranslationParity N hU hI hres hlarge h=0) :
    ∃ a : I → ZMod 2,
      U.map (MulAut.conj (F.physicalFlip a)).toMonoidHom=F.splitAffineAction := by
  let H := (F.sectionTopRepresentation N).ker
  let C := F.rankTwoTranslationChart N hU hI hres hlarge
  have hfirst (h : H) :
      orbitSum H (BinaryAdditiveTwoOrbitChart.leftOrbit H C)
        (F.affineTranslation (F.affineTopLift h))=0 := by
    rw [← BinaryAdditiveTwoOrbitChart.first_parity_eq_orbitSum H C]
    exact hzero h
  rcases hres with ⟨hd,_,_,⟨data⟩,hclasses,_,_⟩
  have hnonempty : Nonempty I := (Nat.card_pos_iff.mp (by rw [hI]; decide)).1
  let i : I := Classical.choice hnonempty
  obtain ⟨o₁,o₂,hne,hcover,hM,_⟩ :=
    permutationBinary_twoBlockCharacter_original_module_eq
      (F.top_isPGroup hU) i hI (F.sectionTopRepresentation N)
      F.kernelTopPermutationSubrepresentation (F.sectionTopIntertwiner N)
      (F.normalSpace N).mkQ_surjective hd data
  change F.kernelSpace=twoOrbitAugmentation H o₁ o₂ at hM
  obtain ⟨g,hg⟩ := exists_orbit_translation H o₁ o₂
  have hgnot : g∉H := by
    intro hm
    have hf := mem_preserves_orbit_of_index_two H data.kernel_index hclasses o₁ g hm
    exact hne (MulAction.orbitRel.Quotient.orbit_injective (hf.symm.trans hg))
  let σ := F.parityRepresentation H o₁ o₂ hne hM
  let z := F.parityCocycle H o₁ o₂ hne hM
  have hact := F.parityRepresentation_apply H o₁ o₂ hne hM
    data.kernel_index hclasses hcover
  have hclass (t : F.top.range) :
      F.parityClass H o₁ o₂ hne hM t=
        F.paritySum H o₁ o₂ (F.affineTranslation (F.affineTopLift t)) := by
    have he := F.parityClass_top H o₁ o₂ hne hM (F.affineTopLift t)
    rw [F.affineTopLift_top] at he
    exact he
  have hz : ∀ t∈H,F.parityClass H o₁ o₂ hne hM t=0 := by
    change ∀ t∈H,z t=0
    rcases hcover (BinaryAdditiveTwoOrbitChart.leftOrbit H C) with ho | ho
    · apply BinarySwapCocycle.zero_on_kernel_of_first_zero H σ hact z g hgnot
      intro t ht
      have hf := hfirst (⟨t,ht⟩:H)
      rw [ho] at hf
      change (F.parityClass H o₁ o₂ hne hM t).1=0
      rw [hclass]
      exact hf
    · apply BinarySwapCocycle.zero_on_kernel_of_second_zero H σ hact z g hgnot
      intro t ht
      have hf := hfirst (⟨t,ht⟩:H)
      rw [ho] at hf
      change (F.parityClass H o₁ o₂ hne hM t).2=0
      rw [hclass]
      exact hf
  exact F.exists_physical_conjugate_eq_split_of_zero_parity H o₁ o₂ hne hM
    data.kernel_index hclasses hcover hz

end SymmetricSubgroupAsymptotics.BinaryPairFrame
