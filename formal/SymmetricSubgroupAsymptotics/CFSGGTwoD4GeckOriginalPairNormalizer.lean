import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleStabilizer
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPairNormalizer
import SymmetricSubgroupAsymptotics.CFSGCentralKernelPSubgroupReflection

/-! The actual original opposed-pair normalizer pulls back to the literal
identity-twisted diagonal normalizer. Central p-element separation reflects
both normalizer conditions through the same original central quotient. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPairNormalizer
open CFSGGTwoD4GeckOriginalProjection CFSGGTwoD4GeckOriginalOppositeAlignment
open CFSGGTwoD4GeckOriginalSimpleParameters CFSGTrialityGeckFixedPairNormalizer
open CFSGTrialityGeckRelativeRootGenerated CFSGTrialityGeckRootGeneratedPGroup
open CFSGTrialityGeckGeneratedSylow CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
local notation "J" => fixedRootGenerated K (RingEquiv.refl K)

def originalPairNormalizer : Subgroup (Projective CartanMatrix.G₂ K) :=
  Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)) ⊓
    Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.G₂ K))

theorem mem_originalPairNormalizer_iff (g : J) :
    generatedToOriginal K g ∈ originalPairNormalizer K p ↔
      g.val ∈ pairNormalizer K (RingEquiv.refl K) := by
  let P := positiveSylow K (RingEquiv.refl K) p
  have hpinj : Function.Injective ((generatedToOriginal K).comp (P : Subgroup J).subtype) := by
    intro x y he
    apply Subtype.ext
    apply generatedToOriginal_injOn_positive K _ _ he
    · simpa only [P,positiveSylow_coe] using x.property
    · simpa only [P,positiveSylow_coe] using y.property
  have hsign (neg : Bool) : generatedToOriginal K g ∈ Subgroup.normalizer
      ((rootPart K (RingEquiv.refl K) neg).map (generatedToOriginal K) : Set _) ↔
      g.val ∈ Subgroup.normalizer (signedFixed K (RingEquiv.refl K) neg : Set _) := by
    rw [CFSGCentralKernelPSubgroupReflection.mem_normalizer_map_iff
      (generatedToOriginal K) P hpinj (generatedToOriginal_kernel_le_center K) _
      (rootPart_isPGroup K (RingEquiv.refl K) p neg)]
    change g ∈ Subgroup.normalizer ((signedFixed K (RingEquiv.refl K) neg).subgroupOf J : Set _) ↔ _
    rw [← Subgroup.subgroupOf_normalizer_eq (signedFixed_le_generated K (RingEquiv.refl K) neg)]
    rfl
  have hpos := hsign false
  have hneg := hsign true
  rw [←originalPositiveSylow_coe K p] at hpos
  change generatedToOriginal K g ∈ Subgroup.normalizer (originalNegative K : Set _) ↔ _ at hneg
  constructor
  · intro h
    exact ⟨⟨hpos.mp h.1,hneg.mp h.2⟩,g.property⟩
  · intro h
    exact ⟨hpos.mpr h.1.1,hneg.mpr h.1.2⟩

theorem originalPairNormalizer_map (f : MulAut (Projective CartanMatrix.G₂ K))
    (hpos : (originalPositiveSylow K p : Subgroup _).map f.toMonoidHom = originalPositiveSylow K p)
    (hneg : (originalNegative K).map f.toMonoidHom = originalNegative K) :
    (originalPairNormalizer K p).map f.toMonoidHom = originalPairNormalizer K p := by
  have hP : (Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K))).map
      f.toMonoidHom = Subgroup.normalizer (originalPositiveSylow K p : Set (Projective CartanMatrix.G₂ K)) :=
    (Subgroup.map_equiv_normalizer_eq
    (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.G₂ K)) f).trans
      (congrArg (fun S : Subgroup (Projective CartanMatrix.G₂ K) => Subgroup.normalizer (S : Set (Projective CartanMatrix.G₂ K))) hpos)
  have hN : (Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.G₂ K))).map
      f.toMonoidHom = Subgroup.normalizer (originalNegative K : Set (Projective CartanMatrix.G₂ K)) :=
    (Subgroup.map_equiv_normalizer_eq (originalNegative K) f).trans
      (congrArg (fun S : Subgroup (Projective CartanMatrix.G₂ K) => Subgroup.normalizer (S : Set (Projective CartanMatrix.G₂ K))) hneg)
  rw [originalPairNormalizer,Subgroup.map_inf _ _ _ f.injective,hP,hN]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPairNormalizer
