import SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopOperatorChart
import SymmetricSubgroupAsymptotics.BinaryPlaneCubicBinaryChart
import SymmetricSubgroupAsymptotics.BinaryTwistedQuartetNormalizedUniform
import SymmetricSubgroupAsymptotics.BinaryUntwistedQuartetNormalizedUniform

/-! Actual faithful A4/S4 quartet tops have uniform TWO on the original
binary translation module. Both the identity and the cubic local twist
are proved, with no odd kernel available or assumed to cancel the twist. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopUniform
open BinaryPlanePermutationAffineEquiv
open BinaryPlaneAlternatingKernelPartition (Frame)
open BinaryPlaneAlternatingCentralizerCommutators (top)
open BinaryPlaneFaithfulTopOperatorChart (Space)

theorem uniform (C : Subgroup Frame) (hinj : Function.Injective (top C))
    (heven : ∀ p : alternatingGroup (Fin 4), ∃ h : C, (h : Frame).right=p.val) :
    UniformSubrepresentationGeneratorBound
      (BinaryPlaneCyclicWreathUniform.representation C) 2 := by
  obtain ⟨F,a,t,L,hL,hA,hT⟩ :=
    BinaryPlaneFaithfulTopOperatorChart.exists_chart C hinj heven
  let rho := BinaryPlaneFaithfulTopOperatorChart.representation C F
  have hu : UniformSubrepresentationGeneratorBound rho 2 := by
    by_cases h1 : L=1
    · apply BinaryUntwistedQuartetNormalizedUniform.uniform rho a t
      · intro v i
        have hh := hA v i
        rw [h1] at hh
        exact hh
      · exact hT
    · obtain ⟨E,hE⟩ := BinaryPlaneCubicBinaryChart.exists_chart L hL h1
      let G : Space ≃ₗ[ZMod 2] Space := LinearEquiv.piCongrRight (fun _ => E)
      let sigma : Representation (ZMod 2) C Space :=
        G.conjRingEquiv.toMonoidHom.comp rho
      have ha : ∀ v i, sigma a v i=
          BinaryTwistedQuartetPolynomial.cubic
            (v (AlternatingFourBinaryActualPolynomialUniform.cycle⁻¹ i)) := by
        intro v i
        change E (rho a (G.symm v) i)=_
        rw [hA,hE]
        change BinaryTwistedQuartetPolynomial.cubic
          (E (E.symm (v (AlternatingFourBinaryActualPolynomialUniform.cycle⁻¹ i))))=_
        rw [E.apply_symm_apply]
      have ht : ∀ v i, sigma t v i=
          v (AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i) := by
        intro v i
        change E (rho t (G.symm v) i)=_
        rw [hT]
        change E (E.symm (v (AlternatingFourBinaryActualPolynomialUniform.flip⁻¹ i)))=_
        rw [E.apply_symm_apply]
      have hs := BinaryTwistedQuartetNormalizedUniform.uniform sigma a t ha ht
      let inter : Representation.IntertwiningMap rho sigma := {
        toLinearMap := G.toLinearMap
        isIntertwining' h := by
          apply LinearMap.ext
          intro v
          change G (rho h v)=G (rho h (G.symm (G v)))
          rw [G.symm_apply_apply] }
      exact hs.of_injective inter G.injective
  let inter : Representation.IntertwiningMap
      (BinaryPlaneCyclicWreathUniform.representation C) rho := {
    toLinearMap := F.toLinearMap
    isIntertwining' h := by
      apply LinearMap.ext
      intro v
      change F (BinaryPlaneCyclicWreathUniform.representation C h v)=
        F (BinaryPlaneCyclicWreathUniform.representation C h (F.symm (F v)))
      rw [F.symm_apply_apply] }
  exact hu.of_injective inter F.injective

end SymmetricSubgroupAsymptotics.BinaryPlaneFaithfulTopUniform
