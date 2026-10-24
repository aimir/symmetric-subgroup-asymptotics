import SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockWeylGeneration
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedOppositeGeneration

/-! The actual four signed simple blocks generate the whole literal
fixed group. Weyl membership comes from original constant words; eight
opposed peels give U, actual opposition gives V, and the already-proved
U/V generation concludes. No simple-root generation premise is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockGeneration
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedBruhatCover CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourMinimalParabolics CFSGReeFFourSimpleBlockPeelingGeneration
open CFSGReeFFourSignedBlockWeylGeneration CFSGReeFFourFixedOppositeGeneration
open CFSGReeFFourSimpleInversionBlocks CFSGReeFFourRelativeOpposition
open CFSGOpposedSubgroupPeeling

theorem opposition_eq_simpleWeyl_power (m : ℕ) :
    oppositionFixed m=(simpleWeyl m false*simpleWeyl m true)^4 := by
  apply Subtype.ext
  change relativeOpposition m=((fixedPairedWord m [false]).val*(fixedPairedWord m [true]).val)^4
  rw [single_paired_word_val,single_paired_word_val]
  rfl

theorem subgroup_eq_top_of_signed_blocks (m : ℕ) (S : Subgroup (originalModelFixed m))
    (hpos : ∀b : Bool,inversionPart (fixedPositive m) (fixedNegative m) (simpleWeyl m b)≤S)
    (hneg : ∀b : Bool,fixedNegative m⊓simpleParabolic m b≤S) : S=⊤ := by
  have hW := simpleWeyl_mem_of_signed_blocks m S hpos hneg
  have hU := positive_le_of_simple_inversions_and_weyls m S hW hpos
  have hO : oppositionFixed m∈S := by
    rw [opposition_eq_simpleWeyl_power]
    exact S.pow_mem (S.mul_mem (hW false) (hW true)) 4
  have hV : fixedNegative m≤S := by
    intro v hv
    have hr : v∈(fixedPositive m).map (MulAut.conj (oppositionFixed m)).toMonoidHom := by
      rw [fixed_positive_image_eq_fixed_negative]
      exact hv
    obtain ⟨u,hu,he⟩ := hr
    rw [←he]
    change oppositionFixed m*u*(oppositionFixed m)⁻¹∈S
    exact S.mul_mem (S.mul_mem hO (hU hu)) (S.inv_mem hO)
  apply eq_top_iff.mpr
  rw [←fixed_positive_sup_negative m]
  exact sup_le hU hV

end SymmetricSubgroupAsymptotics.CFSGReeFFourSignedBlockGeneration
