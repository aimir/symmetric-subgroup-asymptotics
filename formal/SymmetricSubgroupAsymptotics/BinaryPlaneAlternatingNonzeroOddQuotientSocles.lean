import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingOddKernelUniform
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingLinearSocles
import SymmetricSubgroupAsymptotics.OriginalKernelRetainedNonbinaryInterval
import SymmetricSubgroupAsymptotics.OriginalKernelSectionSocleRows
import SymmetricSubgroupAsymptotics.SocleNormalSubgroupGeneratorInheritance
import SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingRetainedComparator
import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelBounds

/-! Whole-socle bound two for EVERY original normal quotient of an actual
nonzero odd-kernel A4/S4 frame. All actual odd ranks use the checked uniform-one theorem. Actual fixed/moving rows share by MAX;
the original denominator is kept literal throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNonzeroOddQuotientSocles
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel OriginalKernelModuleChart
open BinaryPlaneAlternatingKernelPartition (Frame Cubic)

variable {G : Type} [Group G] [Finite G]
  (C : Subgroup Frame)
  (hO : oddKernel C≠⊥)
  (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val)
  (pi : G →* C) (hpi : Function.Surjective pi)
  (A : Rep.{0} (ZMod 2) C) [FiniteDimensional (ZMod 2) A]
  (E : OriginalKernelModuleChart pi A)
  (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
  (hj : Function.Injective j)

include hO heven pi hpi A E j hj in
theorem quotientSocle (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  let O := oddKernel C
  letI : IsMulCommutative O := commutative C
  letI : NeZero (Nat.card O : ZMod 2) := ⟨card_cast_ne_zero C⟩
  have hu1 : UniformSubrepresentationGeneratorBound A.ρ 1 :=
    (BinaryPlaneAlternatingOddKernelUniform.uniform C heven hO).of_injective j hj
  have hu : UniformSubrepresentationGeneratorBound A.ρ 2 := by
    intro S
    exact representationGeneratedBy_mono S.toRepresentation (by decide) (hu1 S)
  have hlocal : ∀ i : Fin 4, ∃ o : O, localLinear C i o≠1 :=
    all_local_nontrivial C hO (BinaryPlaneAlternatingKernelPartition.transitive C heven)
  have hfixed : ∀ a : A, (∀ o : O, A.ρ (o : C) a=a) → a=0 := by
    intro a ha
    apply hj
    have hz := fixedFree C hlocal (j a) (fun o => by
      rw [← Representation.IntertwiningMap.isIntertwining _ _ j (o : C) a,ha o])
    simpa only [map_zero] using hz
  have hsurj : Function.Surjective (sectionTop pi N hpi) := by
    intro y
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) y
    exact ⟨pi g,(sectionTop_apply pi N hpi g).trans hg⟩
  have hlinear : SocleNormalGeneratorBound (G ⧸ (pi.ker ⊔ N)) 2 :=
    BinaryPlaneAlternatingLinearSocles.socle_of_surjective C heven
      (sectionTop pi N hpi) hsurj
  let D := retainedOddSeparator pi N O
  let F := trivialActionSoclePart (G ⧸ N) D
  let f := base pi N
  have hf : Function.Surjective f := base_surjective pi N
  letI : (F.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hFImage : F.map f≤finiteGroupSocle (G ⧸ (pi.ker ⊔ N)) :=
    (Subgroup.map_mono (minimalNormalSoclePart_le_finiteGroupSocle _ _)).trans
      (SocleActionPartQuotientKernel.socle_map_le f hf)
  have hFImageBound : MarkedC4.normalGen (F.map f)≤2 :=
    (MarkedC4.normalGen_le_socle_of_normal_le (F.map f) hFImage).trans
      ((socleNormalGeneratorBound_iff_normalGen_le _ _).mp hlinear)
  have hF : MarkedC4.normalGen F≤2 :=
    (E.fixedSocleRow_normalGen_le_image pi A N hpi O hfixed).trans hFImageBound
  have hM : MarkedC4.normalGen (nontrivialActionSoclePart (G ⧸ N) D)≤2 :=
    E.movingSocleRow_normalGen_le_two pi A N hpi O hu
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr
  exact (normalGen_finiteGroupSocle_le_max_actionSocleParts (G ⧸ N) D).trans (max_le hM hF)

end SymmetricSubgroupAsymptotics.BinaryPlaneAlternatingNonzeroOddQuotientSocles
