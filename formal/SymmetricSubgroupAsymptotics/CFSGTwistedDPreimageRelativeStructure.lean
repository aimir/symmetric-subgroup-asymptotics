import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedElementaryIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedFixed
import SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedRelativeGroup
import SymmetricSubgroupAsymptotics.CFSGCentralCocyclePGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCenterCardinality

/-! The actual natural preimage of the original Fixed action is kept
separate from its literal-fixed kernel. Both index-at-most-two layers
are transported on the same original carriers. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPreimageRelativeStructure
open CFSGOrthogonalDSerreMatrices CFSGTwistedDFixedCentralCocycle
open CFSGTwistedDNaturalFieldTwist CFSGSerreOrdinaryTwists
open CFSGTwistedDFixedElementaryIndex CFSGTwistedDRelativeElementaryGroup

abbrev PreimageGroup (s : ℕ) (q : CFSG.PrimePower) := naturalFixedPreimage s q

def naturalInclusion (s : ℕ) (q : CFSG.PrimePower) :
    PreimageGroup s q →* (Mat (q.Extension 2) (s + 4))ˣ :=
  (elementaryRootGroup (q.Extension 2) (s + 4)).subtype.comp (naturalFixedPreimage s q).subtype

theorem naturalInclusion_injective (s : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (naturalInclusion s q) :=
  Subtype.val_injective.comp Subtype.val_injective

def relativePreimage (s : ℕ) (q : CFSG.PrimePower) : Subgroup (PreimageGroup s q) :=
  (relativeRootGroup (s + 2) q).comap (naturalInclusion s q)

def literalFixedKernel (s : ℕ) (q : CFSG.PrimePower) : Subgroup (PreimageGroup s q) :=
  (fixedElementaryUnits (s + 2) q).comap (naturalInclusion s q)

def centralDifference (s : ℕ) (q : CFSG.PrimePower) :
    PreimageGroup s q →* Subgroup.center (elementaryRootGroup (q.Extension 2) (s + 4)) :=
  CFSGCentralCocyclePGroup.centralDifferenceHom
    (naturalAutomorphism (q.Extension 2) (s + 2) (definingFieldAutomorphism q 2))
    (naturalFixedPreimage s q)
    (fun u => naturalFixedPreimage_central_difference s q u.val u.property)

theorem centralDifference_ker (s : ℕ) (q : CFSG.PrimePower) :
    (centralDifference s q).ker = literalFixedKernel s q := by
  ext u
  constructor
  · intro hu
    have he : u.val⁻¹ * naturalAutomorphism (q.Extension 2) (s + 2)
        (definingFieldAutomorphism q 2) u.val = 1 := congrArg Subtype.val hu
    have hf := (inv_mul_eq_one.mp he).symm
    refine ⟨u.val.property, ?_⟩
    exact congrArg Subtype.val hf
  · intro hu
    have hf : naturalAutomorphism (q.Extension 2) (s + 2)
        (definingFieldAutomorphism q 2) u.val = u.val := Subtype.ext hu.2
    apply Subtype.ext
    change u.val⁻¹ * naturalAutomorphism (q.Extension 2) (s + 2)
      (definingFieldAutomorphism q 2) u.val = 1
    rw [hf, inv_mul_cancel]

instance literalFixedKernel_normal (s : ℕ) (q : CFSG.PrimePower) :
    (literalFixedKernel s q).Normal := by
  rw [← centralDifference_ker]
  infer_instance

theorem literalFixedKernel_index_le_two (s : ℕ) (q : CFSG.PrimePower) :
    (literalFixedKernel s q).index ≤ 2 := by
  rw [← centralDifference_ker, Subgroup.index_ker]
  exact (Nat.card_le_card_of_injective (centralDifference s q).range.subtype
    Subtype.val_injective).trans
      (CFSGOrthogonalDCenterCardinality.center_card_le_two (q.Extension 2) s)

theorem relative_le_literalFixedKernel (s : ℕ) (q : CFSG.PrimePower) :
    relativePreimage s q ≤ literalFixedKernel s q := by
  intro u hu
  exact relative_le_fixedElementary (s + 2) q hu

theorem relative_le_naturalInclusion_range (s : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup (s + 2) q ≤ (naturalInclusion s q).range := by
  intro u hu
  obtain ⟨v, hv, he⟩ :=
    CFSGTwistedDRetainedRelativeGroup.relativeRootGroup_le_derived_unit_image s q hu
  exact ⟨⟨v, CFSGTwistedDDerivedFixed.derived_preimage_le_fixed_preimage s q hv⟩, he⟩

theorem relativePreimage_map (s : ℕ) (q : CFSG.PrimePower) :
    (relativePreimage s q).map (naturalInclusion s q) = relativeRootGroup (s + 2) q :=
  Subgroup.map_comap_eq_self (relative_le_naturalInclusion_range s q)

theorem relativePreimage_index_in_kernel_le_two (s : ℕ) (q : CFSG.PrimePower) :
    ((relativePreimage s q).subgroupOf (literalFixedKernel s q)).index ≤ 2 := by
  let f : literalFixedKernel s q →* fixedElementaryUnits (s + 2) q :=
    ((naturalInclusion s q).comp (literalFixedKernel s q).subtype).codRestrict
      (fixedElementaryUnits (s + 2) q) (fun u => u.property)
  let R := (relativeRootGroup (s + 2) q).subgroupOf (fixedElementaryUnits (s + 2) q)
  change (R.comap f).index ≤ 2
  rw [Subgroup.index_comap]
  have hn : R.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.index_ne_zero_of_finite
  calc
    R.relIndex f.range ≤ R.relIndex ⊤ := Subgroup.relIndex_le_of_le_right le_top hn
    _ = R.index := by rw [Subgroup.relIndex_top_right]
    _ ≤ 2 := relative_index_le_two s q

end SymmetricSubgroupAsymptotics.CFSGTwistedDPreimageRelativeStructure
