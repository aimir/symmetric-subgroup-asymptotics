import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernelStructure
import SymmetricSubgroupAsymptotics.OriginalKernelSectionSocleRows

/-! The structural bounds for an actual extension chart into a cyclic
binary-plane linear wreath image. No independent local Singer hypothesis
or final quotient-socle bound is an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelBounds
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel

variable {R I G : Type} [Group R] [Finite R] [MulAction R I]
  [Fintype I] [DecidableEq I] [Group G]
  (C : Subgroup (W (R := R) (I := I)))
  (pi : G →* C) (A : Rep (ZMod 2) C) (E : OriginalKernelModuleChart pi A)

include pi A E in
/-- A nonbinary actual affine extension has a nonbinary linear image,
because its literal translation kernel is binary. -/
theorem linear_nonbinary (hG : ¬ IsPGroup 2 G) : ¬ IsPGroup 2 C := by
  intro hC
  have hker : IsPGroup 2 pi.ker :=
    (ZModModule.isPGroup_multiplicative (n := 2) (G := A)).of_surjective
      E.equiv.toMonoidHom E.equiv.surjective
  have htop := (hC.to_subgroup (⊤ : Subgroup C)).comap_of_ker_isPGroup pi hker
  apply hG
  intro g
  obtain ⟨n,hn⟩ := htop ⟨g,by trivial⟩
  exact ⟨n,congrArg Subtype.val hn⟩

variable
  (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
  (hj : Function.Injective j)
  (hsurj : Function.Surjective
    ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp C.subtype))
  (c : R) (i₀ : I) (hcycle : ∀ i : I, ∃ n : ℕ, c^n • i₀=i)

include j hj hsurj c i₀ hcycle in
/-- The literal kernel is an invariant submodule of the full two-plane
cyclic frame, so all its invariant subspaces cost at most two. -/
theorem uniform : UniformSubrepresentationGeneratorBound A.ρ 2 :=
  (BinaryPlaneCyclicWreathUniform.uniform_of_surjective C hsurj c i₀ hcycle).of_injective j hj

include hsurj c i₀ hcycle in
theorem actual_block_transitive : ∀ i k : I, ∃ h : C,
    (h : W (R := R) (I := I)).right • i=k := by
  intro i k
  obtain ⟨n,hn⟩ := hcycle i
  obtain ⟨m,hm⟩ := hcycle k
  obtain ⟨h,hh⟩ := hsurj (c^m*(c^n)⁻¹)
  refine ⟨h,?_⟩
  change (h : W (R := R) (I := I)).right=c^m*(c^n)⁻¹ at hh
  rw [hh,mul_smul,← hn,inv_smul_smul]
  exact hm

include j hj hsurj c i₀ hcycle in
/-- Absence of odd fixed vectors descends to the actual correlated kernel
through its injective original intertwiner. -/
theorem kernel_fixedFree (hR : IsPGroup 2 R) (hC : ¬ IsPGroup 2 C) :
    ∀ a : A, (∀ o : oddKernel C, A.ρ (o : C) a=a) → a=0 := by
  intro a ha
  have hja : j a=0 := fixedFree_of_nonbinary C hR hC
    (actual_block_transitive C hsurj c i₀ hcycle) (j a) (fun o ↦ by
      rw [← Representation.IntertwiningMap.isIntertwining _ _ j (o : C) a,ha o])
  apply hj
  simpa only [map_zero] using hja

end SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelBounds
