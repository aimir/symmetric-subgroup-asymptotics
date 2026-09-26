import SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorWords16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierCommutatorForms16T1084
import SymmetricSubgroupAsymptotics.BinaryCarrierDerived16T1084
import SymmetricSubgroupAsymptotics.PrimeDerivedEvaluationPairing
import SymmetricSubgroupAsymptotics.BinaryCarrierQuotientGenerators16T1084
import Mathlib.Algebra.Module.Submodule.Equiv

/-! The numerical commutator forms on six coordinates are the forms of
the same original 16T1084 group. The full seven-generator evaluation span, with its
proved-zero first coordinate removed, makes the coordinate map onto. The actual common-radical certificate then makes it
injective. Thus neither a basis nor an ambient order is assumed when the
single-form and independent-pair radical bounds are transported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1084

abbrev Original := BinaryCarrierDerivedCharacters16T1084.Original
abbrev Characters := BinaryCarrierDerivedCharacters16T1084.Characters
abbrev Input := BinaryCarrierCommutatorForms16T1084.Input
abbrev V := PrimeAbelianization 2 Original

private abbrev g := BinaryCarrierQuotientGenerators16T1084.reducedGenerators
private abbrev kernelIdentity := BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator

/-- Coordinates are evaluations of original generators 1 through 6.
All seven generators remain in the actual ambient group and invariance. -/
def generatorMap : Input →ₗ[ZMod 2] V :=
  BinaryCarrierQuotientGenerators16T1084.generatorMap

theorem generatorMap_surjective : Function.Surjective generatorMap :=
  BinaryCarrierQuotientGenerators16T1084.generatorMap_surjective

/-- The form retains the original whole-group invariant character. -/
def form (χ : Characters) : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2 :=
  derivedEvaluationBilinear 2 kernelIdentity χ

/-- The output-row convention is the transpose of evaluation on a
variable first argument and a fixed second generator. This finite scalar
identity explicitly checks the orientation of all displayed coefficients. -/
theorem matrix_eq_values_transpose :
    ∀ (v : Fin 3 → ZMod 2) (i j : Fin 6),
      BinaryCarrierCommutatorForms16T1084.matrix v i j =
        BinaryCarrierCommutatorWords16T1084.values v j.succ i.succ := by
  decide +kernel

/-- Every numerical output is the actual form evaluated at the same
original second generator. -/
theorem form_generatorMap_eval (χ : Characters) (x : Input) (i : Fin 6) :
    form χ (generatorMap x)
      (primeAbelianizationMap 2 Original (Additive.ofMul (g i))) =
        BinaryCarrierCommutatorForms16T1084.family
          (BinaryCarrierDerivedCharacters16T1084.coordinates χ) x i := by
  change derivedEvaluationBilinear 2 kernelIdentity χ
    (primeAbelianizationGeneratorMap 2 g x)
    (primeAbelianizationMap 2 Original (Additive.ofMul (g i))) = _
  rw [primeAbelianizationGeneratorMap_apply]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, derivedEvaluationBilinear_eval]
  rw [BinaryCarrierCommutatorForms16T1084.family_apply]
  apply Finset.sum_congr rfl
  intro j _
  change x j * derivedCharacterCommutator 2 χ
      (closureGenerators BinaryActionData16.node1084Generators j.succ)
      (closureGenerators BinaryActionData16.node1084Generators i.succ) =
    BinaryCarrierCommutatorForms16T1084.matrix
      (BinaryCarrierDerivedCharacters16T1084.coordinates χ) i j * x j
  rw [BinaryCarrierCommutatorWords16T1084.original_commutator_value,
    matrix_eq_values_transpose, mul_comm]

/-- Vanishing on the six evaluated generators is vanishing on the full
canonical evaluation space, because those actual generators span it. -/
theorem mem_form_ker_generatorMap_iff (χ : Characters) (x : Input) :
    generatorMap x ∈ (form χ).ker ↔
      BinaryCarrierCommutatorForms16T1084.family
        (BinaryCarrierDerivedCharacters16T1084.coordinates χ) x = 0 := by
  constructor
  · intro hx
    funext i
    have h := congrArg
      (fun f : V →ₗ[ZMod 2] ZMod 2 =>
        f (primeAbelianizationMap 2 Original (Additive.ofMul (g i))))
      (LinearMap.mem_ker.mp hx)
    exact (form_generatorMap_eval χ x i).symm.trans h
  · intro hx
    have hgen (i : Fin 6) :
        primeAbelianizationMap 2 Original (Additive.ofMul (g i)) ∈
          (form χ (generatorMap x)).ker :=
      (form_generatorMap_eval χ x i).trans (congrFun hx i)
    have hle : Submodule.span (ZMod 2)
        (Set.range (fun i => primeAbelianizationMap 2 Original (Additive.ofMul (g i)))) ≤
          (form χ (generatorMap x)).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hgen i
    rw [BinaryCarrierQuotientGenerators16T1084.evaluation_reduced_span] at hle
    apply LinearMap.mem_ker.mpr
    ext y
    exact hle (Submodule.mem_top)

theorem form_ker_comap_generatorMap (χ : Characters) :
    (form χ).ker.comap generatorMap =
      (BinaryCarrierCommutatorForms16T1084.family
        (BinaryCarrierDerivedCharacters16T1084.coordinates χ)).ker := by
  ext x
  exact mem_form_ker_generatorMap_iff χ x

/-- Pulling back both slots has precisely the checked numerical kernel;
this equality already holds before injectivity of generatorMap is known. -/
theorem pulled_form_ker_eq (χ : Characters) :
    ((form χ).compl₁₂ generatorMap generatorMap).ker =
      (BinaryCarrierCommutatorForms16T1084.family
        (BinaryCarrierDerivedCharacters16T1084.coordinates χ)).ker := by
  ext x
  change (form χ).compl₁₂ generatorMap generatorMap x = 0 ↔
    BinaryCarrierCommutatorForms16T1084.family
      (BinaryCarrierDerivedCharacters16T1084.coordinates χ) x = 0
  constructor
  · intro hx
    apply (mem_form_ker_generatorMap_iff χ x).mp
    apply LinearMap.mem_ker.mpr
    ext y
    obtain ⟨z, rfl⟩ := generatorMap_surjective y
    exact congrArg (fun f : Input →ₗ[ZMod 2] ZMod 2 => f z) hx
  · intro hx
    have h := LinearMap.mem_ker.mp ((mem_form_ker_generatorMap_iff χ x).mpr hx)
    apply LinearMap.ext
    intro y
    change form χ (generatorMap x) (generatorMap y) = 0
    exact congrArg (fun f : V →ₗ[ZMod 2] ZMod 2 => f (generatorMap y)) h

private def firstCharacter : Characters :=
  BinaryCarrierDerivedCharacters16T1084.coordinateEquiv.symm ![1, 0, 0]

private def secondCharacter : Characters :=
  BinaryCarrierDerivedCharacters16T1084.coordinateEquiv.symm ![0, 1, 0]

private theorem first_coordinates :
    BinaryCarrierDerivedCharacters16T1084.coordinates firstCharacter = ![1, 0, 0] :=
  BinaryCarrierDerivedCharacters16T1084.coordinateEquiv.apply_symm_apply _

private theorem second_coordinates :
    BinaryCarrierDerivedCharacters16T1084.coordinates secondCharacter = ![0, 1, 0] :=
  BinaryCarrierDerivedCharacters16T1084.coordinateEquiv.apply_symm_apply _

/-- Two original invariant characters detect every relation among the
six original evaluations. This proves the coordinate map injective. -/
theorem generatorMap_injective : Function.Injective generatorMap := by
  apply linearMap_injective_of_pullback_common_ker_eq_bot
    generatorMap (form firstCharacter) (form secondCharacter)
  rw [pulled_form_ker_eq, pulled_form_ker_eq, first_coordinates, second_coordinates]
  exact BinaryCarrierCommutatorForms16T1084.family_ker_inf_eq_bot
    ![1, 0, 0] ![0, 1, 0] (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The complete six-coordinate space is equivalent to the original
canonical evaluation space, rather than to an assumed abstract replacement. -/
def generatorEquiv : Input ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofBijective generatorMap ⟨generatorMap_injective, generatorMap_surjective⟩

@[simp] theorem generatorEquiv_apply (x : Input) :
    generatorEquiv x = generatorMap x := rfl

/-- Restriction of the same generator equivalence identifies the actual
radical and its finite certificate. -/
def kernelEquiv (χ : Characters) :
    (BinaryCarrierCommutatorForms16T1084.family
      (BinaryCarrierDerivedCharacters16T1084.coordinates χ)).ker ≃ₗ[ZMod 2]
        (form χ).ker :=
  (LinearEquiv.ofEq _ _ (form_ker_comap_generatorMap χ).symm).trans
    (generatorEquiv.ofSubmodule' (form χ).ker)

private theorem coordinates_ne_zero (χ : Characters) (hχ : χ ≠ 0) :
    BinaryCarrierDerivedCharacters16T1084.coordinates χ ≠ 0 := by
  intro h
  apply hχ
  apply BinaryCarrierDerivedCharacters16T1084.coordinateEquiv.injective
  exact h.trans (map_zero BinaryCarrierDerivedCharacters16T1084.coordinates).symm

/-- The radical of every nonzero actual invariant derived character has
dimension at most two, on the original canonical evaluation space. -/
theorem actual_form_finrank_ker_le_two (χ : Characters) (hχ : χ ≠ 0) :
    Module.finrank (ZMod 2)
      (derivedEvaluationBilinearMap 2
        BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator χ).ker ≤ 2 := by
  change Module.finrank (ZMod 2) (form χ).ker ≤ 2
  rw [← (kernelEquiv χ).finrank_eq]
  exact BinaryCarrierCommutatorForms16T1084.family_finrank_ker_le_two _
    (coordinates_ne_zero χ hχ)

/-- Every independent pair of actual invariant derived characters has
zero common radical. Independence is in the original character space. -/
theorem actual_form_ker_inf_eq_bot_of_independent
    (v : Fin 2 → Characters) (hv : LinearIndependent (ZMod 2) v) :
    (derivedEvaluationBilinearMap 2
      BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator (v 0)).ker ⊓
      (derivedEvaluationBilinearMap 2
        BinaryCarrierDerived16T1084.evaluationKernel_eq_commutator (v 1)).ker = ⊥ := by
  change (form (v 0)).ker ⊓ (form (v 1)).ker = ⊥
  have h0 := coordinates_ne_zero (v 0) (hv.ne_zero 0)
  have h1 := coordinates_ne_zero (v 1) (hv.ne_zero 1)
  have hne : BinaryCarrierDerivedCharacters16T1084.coordinates (v 0) ≠
      BinaryCarrierDerivedCharacters16T1084.coordinates (v 1) := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hv.injective (BinaryCarrierDerivedCharacters16T1084.coordinateEquiv.injective h))
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨x, rfl⟩ := generatorMap_surjective y
  have hx := BinaryCarrierCommutatorForms16T1084.family_joint_zero
    _ _ h0 h1 hne x
    ((mem_form_ker_generatorMap_iff (v 0) x).mp hy.1)
    ((mem_form_ker_generatorMap_iff (v 1) x).mp hy.2)
  apply (Submodule.mem_bot (R := ZMod 2)).mpr
  rw [hx, map_zero]

end SymmetricSubgroupAsymptotics.BinaryCarrierFormTransport16T1084
