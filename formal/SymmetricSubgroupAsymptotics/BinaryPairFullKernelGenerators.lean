import SymmetricSubgroupAsymptotics.BinaryPairPermutationGeneratorExtension
import SymmetricSubgroupAsymptotics.ModuleGeneratorKernelSharing
import SymmetricSubgroupAsymptotics.RepresentationModuleGeneratorTransport

/-! Independent flips of all physical pairs force every invariant subspace
outside the pair-sum kernel to contain that entire kernel. Consequently
the uniform generator budget of the pair module also bounds the point
module. The original group and its literal pair frame are retained. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} [Fintype I] [DecidableEq I]
  {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

/-- Full independent pair flips and transitivity on pairs make the
pair-constant kernel comparable with every invariant subspace. -/
theorem pairSum_kernel_comparable
    (hflip : ∀ i : I, ∃ k : F.top.ker,
      F.bits k = Pi.single i (1 : ZMod 2))
    (htrans : ∀ i j : I, ∃ u : U, F.top u i = j)
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) U X))
    (hW : ¬ W.toSubmodule ≤ F.pairSum.ker) :
    F.pairSum.ker ≤ W.toSubmodule := by
  have hv : ∃ v ∈ W.toSubmodule, F.pairSum v ≠ 0 := by
    by_contra hn
    apply hW
    intro v hv
    change F.pairSum v = 0
    by_contra hz
    exact hn ⟨v, hv, hz⟩
  obtain ⟨v, hv, hsum⟩ := hv
  have hi : ∃ i, F.pairSum v i ≠ 0 := by
    by_contra hn
    apply hsum
    funext i
    by_contra hz
    exact hn ⟨i, hz⟩
  obtain ⟨i, hi⟩ := hi
  have hi1 : F.pairSum v i = 1 := by
    have hcases (a : ZMod 2) : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact (hcases _).resolve_left hi
  obtain ⟨k, hk⟩ := hflip i
  have hdelta : F.pairConstant (Pi.single i (1 : ZMod 2)) ∈ W.toSubmodule := by
    have h := W.toSubmodule.sub_mem (W.apply_mem_toSubmodule (k : U) hv) hv
    rw [F.kernel_displacement_eq_pairConstant_product, hk] at h
    have he : (fun j ↦ (Pi.single i 1 : I → ZMod 2) j * F.pairSum v j) =
        (Pi.single i 1 : I → ZMod 2) := by
      funext j
      by_cases hj : i = j
      · subst j; simp [hi1]
      · simp [hj]
    rwa [he] at h
  have hall (j : I) : F.pairConstant (Pi.single j (1 : ZMod 2)) ∈ W.toSubmodule := by
    obtain ⟨u, hu⟩ := htrans i j
    have h := W.apply_mem_toSubmodule u hdelta
    rw [F.pairConstant_action] at h
    have he : (fun t ↦ (Pi.single i 1 : I → ZMod 2) ((F.top u)⁻¹ t)) =
        (Pi.single j 1 : I → ZMod 2) := by
      funext t
      have ht : (F.top u)⁻¹ t = i ↔ t = j := by
        constructor
        · intro hit
          calc
            t = F.top u ((F.top u)⁻¹ t) := ((F.top u).apply_symm_apply t).symm
            _ = F.top u i := congrArg (F.top u) hit
            _ = j := hu
        · intro htj
          rw [htj, ← hu]
          exact (F.top u).symm_apply_apply i
      simp only [Pi.single_apply, ht]
    rwa [he] at h
  have hconstant (a : I → ZMod 2) : F.pairConstant a ∈ W.toSubmodule := by
    have hdecomp : (∑ i, a i • Pi.single i (1 : ZMod 2)) = a := by
      calc
        _ = ∑ i, Pi.single i (a i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Pi.single_smul]
          simp
        _ = a := LinearMap.sum_single_apply (fun _ : I ↦ ZMod 2) a
    rw [← hdecomp, map_sum]
    exact W.toSubmodule.sum_mem fun i _ ↦ by
      rw [map_smul]
      exact W.toSubmodule.smul_mem _ (hall i)
  intro f hf
  have hf' : f ∈ LinearMap.range F.pairConstantIntertwiner.toLinearMap := by
    rw [F.pairConstant_pairSum_exact_linear]
    exact hf
  obtain ⟨a, rfl⟩ := hf'
  exact hconstant a

/-- With all individual pair flips present, the point module shares the
pair module's generator positions even though the extension need not split. -/
theorem uniform_of_full_pair_kernel
    (hflip : ∀ i : I, ∃ k : F.top.ker,
      F.bits k = Pi.single i (1 : ZMod 2))
    (htrans : ∀ i j : I, ∃ u : U, F.top u i = j)
    (n : ℕ)
    (hpair : UniformSubrepresentationGeneratorBound F.pulledBackCoordinateTopAction n) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) n := by
  let rho := permutationFunctionRepresentation (ZMod 2) U X
  let sigma := F.pulledBackCoordinateTopAction
  let i : sigma.asModule →ₗ[(ZMod 2)[U]] rho.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule sigma rho
      F.pairConstantIntertwiner
  let q : rho.asModule →ₗ[(ZMod 2)[U]] sigma.asModule :=
    Representation.IntertwiningMap.equivLinearMapAsModule rho sigma
      F.pairSumIntertwiner
  apply (uniformSubrepresentationGeneratorBound_iff_submodule rho n).mpr
  have hp := (uniformSubrepresentationGeneratorBound_iff_submodule sigma n).mp hpair
  apply ModuleGeneratedBy.uniform_of_comparable_exact i q
    F.pairConstantIntertwiner_injective F.pairConstant_pairSum_exact n hp hp
  intro S hS
  let W : Subrepresentation rho := Subrepresentation.ofSubmodule' S
  have hW : ¬ W.toSubmodule ≤ F.pairSum.ker := by
    intro h
    apply hS
    intro x hx
    exact h hx
  exact F.pairSum_kernel_comparable hflip htrans W hW

/-- The same theorem stated on the intrinsic range of the actual pair top. -/
theorem uniform_of_full_pair_kernel_coordinateTop
    (hflip : ∀ i : I, ∃ k : F.top.ker,
      F.bits k = Pi.single i (1 : ZMod 2))
    (htrans : ∀ i j : I, ∃ u : U, F.top u i = j)
    (n : ℕ)
    (hpair : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) F.top.range I) n) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) U X) n :=
  F.uniform_of_full_pair_kernel hflip htrans n
    (UniformSubrepresentationGeneratorBound.comp_of_surjective
      (permutationFunctionRepresentation (ZMod 2) F.top.range I)
      F.top.rangeRestrict F.top.rangeRestrict_surjective hpair)

end SymmetricSubgroupAsymptotics.BinaryPairFrame

end
