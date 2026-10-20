import SymmetricSubgroupAsymptotics.AlternatingFourBinaryActualPolynomialUniform
import SymmetricSubgroupAsymptotics.AlternatingTopImageNormalGenerators
import SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import SymmetricSubgroupAsymptotics.TernaryPermutationWreathEmbedding

/-! All actual subgroups of the binary-sign wreath with A4/S4 top have
ambient normal-generator bound two. The modular extension is kept
nonsplit: the actual binary kernel module contributes one and its literal
top image contributes one. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingSignedImageNormalGenerators
open LinearSemidirectSubgroupKernelChart
abbrev Top := Equiv.Perm (Fin 4)
abbrev ESign := TernaryPermutationWreathEmbedding.signs (R := Top) (I := Fin 4)
abbrev action := CyclicOrbitBinarySignNormalGenerators.linearAction ESign
abbrev Model := CyclicOrbitBinarySignNormalGenerators.Model ESign

private theorem cycle_even : AlternatingFourBinaryActualPolynomialUniform.cycle∈
    alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign _=1
  decide +kernel
private theorem flip_even : AlternatingFourBinaryActualPolynomialUniform.flip∈
    alternatingGroup (Fin 4) := by
  change Equiv.Perm.sign _=1
  decide +kernel

variable (B : Subgroup Model)

abbrev blockImage := Image action B
abbrev ambient : Representation (ZMod 2) (blockImage B) (Fin 4 → ZMod 2) :=
  (CyclicOrbitBinarySignNormalGenerators.permutationRepresentation
    (R := Top) (X := Fin 4)).comp (blockImage B).subtype

theorem ambient_uniform (heven : alternatingGroup (Fin 4)≤blockImage B) :
    UniformSubrepresentationGeneratorBound (ambient B) 1 := by
  let a : blockImage B := ⟨AlternatingFourBinaryActualPolynomialUniform.cycle,heven cycle_even⟩
  let t : blockImage B := ⟨AlternatingFourBinaryActualPolynomialUniform.flip,heven flip_even⟩
  exact AlternatingFourBinaryActualPolynomialUniform.uniform (ambient B) a t
    (fun _ _ => rfl) (fun _ _ => rfl)

theorem normalGen_le_two (heven : alternatingGroup (Fin 4)≤blockImage B)
    (N : Subgroup B) [N.Normal] : MarkedC4.normalGen N≤2 := by
  let pi := LinearSemidirectActualImageKernelChart.top action B
  let A := LinearSemidirectActualImageKernelChart.kernelModule action B
  let E := LinearSemidirectActualImageKernelChart.originalKernelChart action B
  have hpi : Function.Surjective pi := (projection action B).rangeRestrict_surjective
  let j0 := LinearSemidirectActualImageKernelChart.inclusion action B
  let j : Representation.IntertwiningMap A.ρ (ambient B) :=
    { toLinearMap := ESign.toSubmodule.subtype.comp j0.toLinearMap
      isIntertwining' t := by
        apply LinearMap.ext
        intro v
        exact congrArg Subtype.val
          (Representation.IntertwiningMap.isIntertwining _ _ j0 t v) }
  have hj : Function.Injective j := Subtype.val_injective.comp
    (LinearSemidirectActualImageKernelChart.inclusion_injective action B)
  have hu : UniformSubrepresentationGeneratorBound A.ρ 1 :=
    (ambient_uniform B heven).of_injective j hj
  let eqQ := QuotientGroup.quotientKerEquivOfSurjective pi hpi
  have htop : ∀ M : Subgroup (blockImage B), M.Normal → MarkedC4.normalGen M≤1 := by
    intro M hM
    obtain ⟨x,hx⟩ := AlternatingTopImageNormalGenerators.normal_generating_singletons
      (blockImage B) heven M hM
    exact normalGen_le_of_fin_tuple x hx
  have hquot : ∀ M : Subgroup (B ⧸ pi.ker), M.Normal → MarkedC4.normalGen M≤1 := by
    intro M hM
    letI := hM
    exact CoprimeKernelQuotientSocles.normalGen_image_bound eqQ.symm.toMonoidHom
      eqQ.symm.surjective 1 htop M
  exact ElementaryUniformNormalGenerators.normalGen_le pi.ker (E.elementaryChart pi A)
    1 1 (E.elementaryChart_uniform pi A hpi 1 hu) hquot N

theorem normal_generating_pairs (heven : alternatingGroup (Fin 4)≤blockImage B) :
    ∀ N : Subgroup B, N.Normal →
      ∃ x : Fin 2 → B, Subgroup.normalClosure (Set.range x)=N := by
  intro N hN
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N (normalGen_le_two B heven N)

end SymmetricSubgroupAsymptotics.AlternatingSignedImageNormalGenerators
