import SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelOrbitUniform
import SymmetricSubgroupAsymptotics.BinaryCubicProperTopUniform
import SymmetricSubgroupAsymptotics.BinaryCubicTransitiveCyclic

/-! The two-block state uses the actual global binary action, which
may be semilinear outside the cubic centralizer. Its ambient supported
seed is cyclic; every proper invariant scalar subspace has dimension
at most one. No scalar-linear action of the larger group is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelTwoBlockUniform
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel
open BinaryPlaneOddKernelMultiplicityUniform (localKernel)
open BinaryPlaneSingleKernelScalarAction
open BinaryPlaneSingleKernelCentralizerOrbits (blockAction)
open BinaryQuadraticField (Scalar omega)

variable {R I : Type} [Group R] [Finite R] [MulAction R I]
    [Fintype I] [DecidableEq I]
    (C : Subgroup (W (R := R) (I := I))) (i₀ : I)
    (hsingle : ∀ i : I, localKernel C i = localKernel C i₀)
    (hO : oddKernel C ≠ ⊥)

/-- The actual whole-group action is conjugated only as an F2 action. -/
def representation : Representation (ZMod 2) C (I → Scalar) :=
  (functionChart C i₀ hsingle hO).conjRingEquiv.toMonoidHom.comp
    (BinaryPlaneCyclicWreathUniform.representation C)

private theorem chart_single (i : I) (v : Plane) :
    functionChart C i₀ hsingle hO (Pi.single i v) =
      Pi.single i (coordinateChart C i₀ hsingle hO i v) := by
  funext j
  change coordinateChart C i₀ hsingle hO j ((Pi.single i v : I → Plane) j) =
    (Pi.single i (coordinateChart C i₀ hsingle hO i v) : I → Scalar) j
  by_cases hj : j = i
  · subst j
    rw [Pi.single_eq_same,Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hj,map_zero]

private theorem chart_symm_single (i : I) (a : Scalar) :
    (functionChart C i₀ hsingle hO).symm (Pi.single i a) =
      Pi.single i ((coordinateChart C i₀ hsingle hO i).symm a) := by
  apply (functionChart C i₀ hsingle hO).injective
  rw [LinearEquiv.apply_symm_apply,chart_single,LinearEquiv.apply_symm_apply]

omit [Finite R] [Fintype I] in
private theorem raw_single (g : C) (i : I) (v : Plane) :
    BinaryPlaneCyclicWreathUniform.representation C g (Pi.single i v) =
      Pi.single ((g : W (R := R) (I := I)).right • i)
        ((g : W (R := R) (I := I)).left ((g : W (R := R) (I := I)).right • i) v) := by
  let w : W (R := R) (I := I) := g.val
  funext j
  change w.left j ((Pi.single i v : I → Plane) (w.right⁻¹ • j)) =
    (Pi.single (w.right • i) (w.left (w.right • i) v) : I → Plane) j
  by_cases hj : j = w.right • i
  · subst j
    rw [inv_smul_smul,Pi.single_eq_same,Pi.single_eq_same]
  · have hn : w.right⁻¹ • j ≠ i := by
      intro h
      apply hj
      calc
        j = w.right • (w.right⁻¹ • j) := (smul_inv_smul _ _).symm
        _ = w.right • i := congrArg (fun z => w.right • z) h
    rw [Pi.single_eq_of_ne hn,Pi.single_eq_of_ne hj,map_zero]

/-- Only the supported seed 1 is tested here; no scalar linearity of
the whole-group operator is needed. -/
theorem supported_seed (g : C) (i : I) : ∃ a : Scalarˣ,
    representation C i₀ hsingle hO g (Pi.single i 1) =
      (a : Scalar) • (Pi.single ((g : W (R := R) (I := I)).right • i) 1 : I → Scalar) := by
  let w : W (R := R) (I := I) := g
  let j := w.right • i
  let c : Scalar := coordinateChart C i₀ hsingle hO j
    (w.left j ((coordinateChart C i₀ hsingle hO i).symm 1))
  have hc : c ≠ 0 := by
    intro hz
    have h1 := (coordinateChart C i₀ hsingle hO j).injective
      (hz.trans (map_zero (coordinateChart C i₀ hsingle hO j)).symm)
    have h2 := (w.left j).injective (h1.trans (map_zero (w.left j)).symm)
    have h3 := congrArg (coordinateChart C i₀ hsingle hO i) h2
    have h10 : (1 : Scalar) = 0 := by
      simpa only [LinearEquiv.apply_symm_apply,map_zero] using h3
    exact one_ne_zero h10
  refine ⟨Units.mk0 c hc,?_⟩
  change functionChart C i₀ hsingle hO
    (BinaryPlaneCyclicWreathUniform.representation C g
      ((functionChart C i₀ hsingle hO).symm (Pi.single i 1))) = _
  rw [chart_symm_single,raw_single,chart_single]
  change (Pi.single j c : I → Scalar) =
    (↑(Units.mk0 c hc) : Scalar) • (Pi.single j 1 : I → Scalar)
  rw [←Pi.single_smul]
  simp only [Units.val_mk0,smul_eq_mul,mul_one]

include hsingle hO in
theorem generatedBy_one
    (htrans : ∀ i j : I, ∃ g : C, (g : W (R := R) (I := I)).right • i = j) :
    RepresentationGeneratedBy (representation C i₀ hsingle hO) 1 := by
  letI := blockAction C
  letI : Nonempty I := ⟨i₀⟩
  letI : MulAction.IsPretransitive C I := ⟨htrans⟩
  apply BinaryCubicTransitiveCyclic.generatedBy_one
    (representation C i₀ hsingle hO) (centralizer C)
    (scalarRepresentation C i₀ hsingle hO)
    (scalarRepresentation_apply C i₀ hsingle hO)
    (scalarGenerator C i₀ hsingle hO) (scalarGenerator_action C i₀ hsingle hO)
  exact supported_seed C i₀ hsingle hO

include hsingle hO in
theorem uniform_one_of_card_two
    (htrans : ∀ i j : I, ∃ g : C, (g : W (R := R) (I := I)).right • i = j)
    (hcard : Nat.card I = 2) :
    UniformSubrepresentationGeneratorBound (BinaryPlaneCyclicWreathUniform.representation C) 1 := by
  let rho := representation C i₀ hsingle hO
  have hdim : Module.finrank Scalar (I → Scalar) ≤ 2 := by
    rw [Module.finrank_pi,←Nat.card_eq_fintype_card,hcard]
  have hu := BinaryCubicProperTopUniform.uniform_one rho (centralizer C)
    (scalarRepresentation C i₀ hsingle hO)
    (scalarRepresentation_apply C i₀ hsingle hO)
    (scalarGenerator C i₀ hsingle hO) (scalarGenerator_action C i₀ hsingle hO)
    hdim (generatedBy_one C i₀ hsingle hO htrans)
  let F := functionChart C i₀ hsingle hO
  let inter : Representation.IntertwiningMap
      (BinaryPlaneCyclicWreathUniform.representation C) rho := {
    toLinearMap := F.toLinearMap
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      change F (BinaryPlaneCyclicWreathUniform.representation C g v) =
        F (BinaryPlaneCyclicWreathUniform.representation C g (F.symm (F v)))
      rw [F.symm_apply_apply] }
  exact hu.of_injective inter F.injective

include hsingle hO in
/-- All sizes are now retained, including the genuine semilinear
two-block state. This remains a uniform module bound, not the full MN theorem. -/
theorem uniform [Nontrivial I]
    (htrans : ∀ i j : I, ∃ g : C, (g : W (R := R) (I := I)).right • i = j) :
    UniformSubrepresentationGeneratorBound (BinaryPlaneCyclicWreathUniform.representation C)
      (Nat.card I / 2) := by
  by_cases hcard : Nat.card I = 2
  · have hu := uniform_one_of_card_two C i₀ hsingle hO htrans hcard
    rw [hcard]
    exact hu
  · exact BinaryPlaneSingleKernelOrbitUniform.uniform_of_degree_ne_two
      C i₀ hsingle hO htrans hcard

end SymmetricSubgroupAsymptotics.BinaryPlaneSingleKernelTwoBlockUniform
