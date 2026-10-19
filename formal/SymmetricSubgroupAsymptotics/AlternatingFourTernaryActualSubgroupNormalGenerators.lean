import SymmetricSubgroupAsymptotics.TernarySignedPermutationSubgroupSocles
import SymmetricSubgroupAsymptotics.AlternatingSignedImageNormalGenerators
import SymmetricSubgroupAsymptotics.TernaryFourMonomialUniform

/-! Three normal generators for every actual subgroup of the signed
four-ternary affine group whose actual block image contains A4. Both
binary signs and ternary offsets may be nonsplit and correlated. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingFourTernaryActualSubgroupNormalGenerators
open LinearSemidirectSubgroupKernelChart
abbrev E := AlternatingSignedImageNormalGenerators.ESign
abbrev action := TernarySignedPermutationSubgroupSocles.linearAction E
abbrev Model := TernarySignedPermutationSubgroupSocles.Model E
abbrev SignedImage (K : Subgroup Model) := Image action K

private theorem even_reference : ∀ x y : Fin 4,
    ∃ g : Equiv.Perm (Fin 4), Equiv.Perm.sign g = 1 ∧ g x = y := by decide +kernel

variable (K : Subgroup Model)

theorem ambient_uniform
    (heven : alternatingGroup (Fin 4) ≤
      AlternatingSignedImageNormalGenerators.blockImage (SignedImage K)) :
    UniformSubrepresentationGeneratorBound (imageRepresentation action K) 1 := by
  let b : SignedImage K →* Equiv.Perm (Fin 4) :=
    (TernarySignedPermutationSubgroupSocles.blockPermutation E).comp (SignedImage K).subtype
  let d : SignedImage K → Fin 4 → ZMod 3 :=
    fun g => TernarySignedPermutationSubgroupSocles.coefficient E g
  have h1 : ∀ i, d 1 i = 1 := TernarySignedPermutationSubgroupSocles.coefficient_one E
  have hm : ∀ g h i, d (g*h) i = d g i * d h (b g⁻¹ i) :=
    fun g h i => TernarySignedPermutationSubgroupSocles.coefficient_mul E g h i
  change UniformSubrepresentationGeneratorBound
    (TernaryMonomialOrbitUniform.representation b d h1 hm) 1
  apply TernaryFourMonomialUniform.uniform b d h1 hm
  intro x y
  obtain ⟨g,hg,hxy⟩ := even_reference x y
  have hgA : g ∈ alternatingGroup (Fin 4) := hg
  obtain ⟨s,hs⟩ := heven hgA
  refine ⟨s,?_⟩
  change (s.val.right : Equiv.Perm (Fin 4)) x = y
  change s.val.right = g at hs
  rw [hs]
  exact hxy

theorem normalGen_le_three
    (heven : alternatingGroup (Fin 4) ≤
      AlternatingSignedImageNormalGenerators.blockImage (SignedImage K))
    (N : Subgroup K) [N.Normal] : MarkedC4.normalGen N ≤ 3 := by
  apply LinearSemidirectSubgroupSocles.normalGen_le action K 1 2 (ambient_uniform K heven)
  intro L hL
  letI := hL
  exact AlternatingSignedImageNormalGenerators.normalGen_le_two (SignedImage K) heven L

theorem normal_generating_triples
    (heven : alternatingGroup (Fin 4) ≤
      AlternatingSignedImageNormalGenerators.blockImage (SignedImage K)) :
    ∀ N : Subgroup K, N.Normal →
      ∃ x : Fin 3 → K, Subgroup.normalClosure (Set.range x) = N := by
  intro N hN
  letI := hN
  exact exists_normal_generating_tuple_of_normalGen_le N (normalGen_le_three K heven N)

theorem socle_of_surjective
    (heven : alternatingGroup (Fin 4) ≤
      AlternatingSignedImageNormalGenerators.blockImage (SignedImage K))
    {Q : Type} [Group Q] (pi : K →* Q) (hpi : Function.Surjective pi) :
    SocleNormalGeneratorBound Q 3 :=
  normal_generating_tuples_of_surjective pi hpi (normal_generating_triples K heven)
    (finiteGroupSocle Q) inferInstance

end SymmetricSubgroupAsymptotics.AlternatingFourTernaryActualSubgroupNormalGenerators
