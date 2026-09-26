import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.BilinearMap

/-! Coordinates from a finite tuple of original generators into the
canonical prime evaluation space. Generation proves surjectivity, without
an evaluation-kernel/derived-subgroup identity. A zero common radical of
two actual pulled-back forms proves injectivity of that same map. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

section Pullback

variable {k E V U : Type*} [Field k]
    [AddCommGroup E] [Module k E]
    [AddCommGroup V] [Module k V]
    [AddCommGroup U] [Module k U]

/-- A vector lost by f lies in the left radical of every bilinear form
pulled back along f in both slots. No symmetry or alternation is needed. -/
theorem linearMap_ker_le_pullback_bilinear_ker
    (f : E →ₗ[k] V) (B : V →ₗ[k] V →ₗ[k] U) :
    f.ker ≤ (B.compl₁₂ f f).ker := by
  intro x hx
  apply LinearMap.mem_ker.mpr
  ext y
  change B (f x) (f y) = 0
  rw [show f x = 0 from hx, map_zero, LinearMap.zero_apply]

/-- Common radical zero certifies injectivity of the original coordinate
map itself; it cannot hold merely by discarding the kernel of that map. -/
theorem linearMap_injective_of_pullback_common_ker_eq_bot
    (f : E →ₗ[k] V) (B C : V →ₗ[k] V →ₗ[k] U)
    (hcommon : (B.compl₁₂ f f).ker ⊓ (C.compl₁₂ f f).ker = ⊥) :
    Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  exact (le_inf (linearMap_ker_le_pullback_bilinear_ker f B)
    (linearMap_ker_le_pullback_bilinear_ker f C)).trans hcommon.le

end Pullback

variable (p : ℕ) [Fact p.Prime]
    {G ι : Type*} [Group G] [Fintype ι]

/-- The coefficient vector is sent to the displayed linear combination
of evaluations of the same original tuple. -/
def primeAbelianizationGeneratorMap (g : ι → G) :
    (ι → ZMod p) →ₗ[ZMod p] PrimeAbelianization p G :=
  ∑ i, (LinearMap.proj i : (ι → ZMod p) →ₗ[ZMod p] ZMod p).smulRight
    (primeAbelianizationMap p G (Additive.ofMul (g i)))

theorem primeAbelianizationGeneratorMap_apply (g : ι → G) (c : ι → ZMod p) :
    primeAbelianizationGeneratorMap p g c =
      ∑ i, c i • primeAbelianizationMap p G (Additive.ofMul (g i)) := by
  simp only [primeAbelianizationGeneratorMap, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply]

@[simp]
theorem primeAbelianizationGeneratorMap_single (g : ι → G) (i : ι) (c : ZMod p) :
    primeAbelianizationGeneratorMap p g (Pi.single i c) =
      c • primeAbelianizationMap p G (Additive.ofMul (g i)) := by
  simp [primeAbelianizationGeneratorMap_apply, Pi.single_apply]

@[simp]
theorem primeAbelianizationGeneratorMap_basis (g : ι → G) (i : ι) :
    primeAbelianizationGeneratorMap p g (Pi.single i (1 : ZMod p)) =
      primeAbelianizationMap p G (Additive.ofMul (g i)) := by
  rw [primeAbelianizationGeneratorMap_single, one_smul]

/-- Actual group generation spans the canonical prime evaluation space.
No p-group assumption or derived-kernel identification is used. -/
theorem primeAbelianizationGeneratorMap_surjective [Finite G]
    (g : ι → G) (hg : Subgroup.closure (Set.range g) = ⊤) :
    Function.Surjective (primeAbelianizationGeneratorMap p g) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← primeEvaluation_span_eq_top_of_generates p g hg]
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨Pi.single i 1, primeAbelianizationGeneratorMap_basis p g i⟩

/-- A common-radical certificate proves that the original generator
coordinates, not a quotient of them, identify the actual evaluation space. -/
def primeAbelianizationGeneratorEquiv_of_common_radical [Finite G]
    (g : ι → G) (hg : Subgroup.closure (Set.range g) = ⊤)
    (B C : PrimeAbelianization p G →ₗ[ZMod p]
      PrimeAbelianization p G →ₗ[ZMod p] ZMod p)
    (hcommon :
      (B.compl₁₂ (primeAbelianizationGeneratorMap p g)
        (primeAbelianizationGeneratorMap p g)).ker ⊓
      (C.compl₁₂ (primeAbelianizationGeneratorMap p g)
        (primeAbelianizationGeneratorMap p g)).ker = ⊥) :
    (ι → ZMod p) ≃ₗ[ZMod p] PrimeAbelianization p G :=
  LinearEquiv.ofBijective (primeAbelianizationGeneratorMap p g)
    ⟨linearMap_injective_of_pullback_common_ker_eq_bot _ B C hcommon,
      primeAbelianizationGeneratorMap_surjective p g hg⟩

@[simp]
theorem primeAbelianizationGeneratorEquiv_of_common_radical_apply [Finite G]
    (g : ι → G) (hg : Subgroup.closure (Set.range g) = ⊤)
    (B C : PrimeAbelianization p G →ₗ[ZMod p]
      PrimeAbelianization p G →ₗ[ZMod p] ZMod p)
    (hcommon :
      (B.compl₁₂ (primeAbelianizationGeneratorMap p g)
        (primeAbelianizationGeneratorMap p g)).ker ⊓
      (C.compl₁₂ (primeAbelianizationGeneratorMap p g)
        (primeAbelianizationGeneratorMap p g)).ker = ⊥)
    (c : ι → ZMod p) :
    primeAbelianizationGeneratorEquiv_of_common_radical p g hg B C hcommon c =
      primeAbelianizationGeneratorMap p g c := rfl

end SymmetricSubgroupAsymptotics
