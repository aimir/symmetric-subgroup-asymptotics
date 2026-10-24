import SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelScalarMonomial
import SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelCentralizerOrbits
import SymmetricSubgroupAsymptotics.MonomialTwoOrbitUniform

/-! A single actual nonzero cubic kernel class has half-degree capacity
on every transitive block carrier except the explicitly retained
two-block state. The two centralizer orbit images remain correlated. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelOrbitUniform
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open BinaryPlaneSingleKernelScalarAction
open BinaryPlaneSingleKernelCentralizerOrbits (blockAction)
open BinaryQuadraticField (Scalar)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I] [Nontrivial I]
    (C : Subgroup (W (R := R) (I := I))) (i₀ : I)
    (hsingle : ∀ i : I, localKernel C i = localKernel C i₀)
    (hO : oddKernel C ≠ ⊥)
    (htrans : ∀ i j : I, ∃ h : C, (h : W (R := R) (I := I)).right • i = j)

include hsingle hO htrans in
theorem uniform_of_degree_ne_two (hnot : Nat.card I ≠ 2) :
    UniformSubrepresentationGeneratorBound (BinaryPlaneCyclicWreathUniform.representation C)
      (Nat.card I / 2) := by
  letI := blockAction C
  rcases BinaryPlaneSingleKernelCentralizerOrbits.orbit_alternative
    C i₀ hsingle hO htrans with htransH | ⟨htwo,hsize⟩
  · exact BinaryPlaneSingleKernelScalarMonomial.uniform_of_centralizer_transitive
      C i₀ hsingle hO htransH
  · let H := centralizer C
    let rho2 := binaryRepresentation C i₀ hsingle hO
    let rho4 := scalarRepresentation C i₀ hsingle hO
    have hdelta : ∀ g : H, ∀ x : I, ∃ u : Scalarˣ,
        rho4 g (Pi.single x 1) = (u : Scalar) • (Pi.single (g • x) 1 : I → Scalar) := by
      intro g x
      obtain ⟨u,hu⟩ := BinaryPlaneSingleKernelScalarMonomial.scalar_monomial
        C i₀ hsingle hO g x
      refine ⟨u,?_⟩
      convert hu using 1 <;> solve
        | rfl
        | dsimp only [rho4]
          congr 1
          funext j
          by_cases hj : j = x <;> simp [Pi.single,Function.update,hj]
        | funext j
          have hact : g • x = (((g : C) : W (R := R) (I := I)).right • x) := rfl
          rw [hact]
          by_cases hj : j = (((g : C) : W (R := R) (I := I)).right • x)
          · simp [Pi.single,Function.update,hj]
          · simp [Pi.single,Function.update,hj]
    have hdegree : 4 ≤ Nat.card I := by
      have hp : 1 < Nat.card I := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      have hs := hsize (Quotient.mk'' i₀)
      omega
    have hu4 := MonomialTwoOrbitUniform.uniform_of_two_equal_orbits
      rho4 hdelta htwo hsize hdegree
    have hu2 := BinaryCubicScalarGeneratorTransfer.uniform rho2 rho4
      (scalarRepresentation_apply C i₀ hsingle hO) (scalarGenerator C i₀ hsingle hO)
      (scalarGenerator_action C i₀ hsingle hO) hu4
    let rhoH := (BinaryPlaneCyclicWreathUniform.representation C).comp H.subtype
    let F := functionChart C i₀ hsingle hO
    let inter : Representation.IntertwiningMap rhoH rho2 := {
      toLinearMap := F.toLinearMap
      isIntertwining' h := by
        apply LinearMap.ext
        intro v
        change F (rhoH h v) = F (rhoH h (F.symm (F v)))
        rw [F.symm_apply_apply] }
    exact UniformSubrepresentationGeneratorBound.of_comp
      (BinaryPlaneCyclicWreathUniform.representation C) H.subtype
        (hu2.of_injective inter F.injective)

end SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelOrbitUniform
