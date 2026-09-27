import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Pi

/-!
# Joint coordinates of independent original characters

Independence of a finite family of prime-field characters on one original
finite group implies surjectivity onto all of their coordinates jointly.
The proof evaluates the retained character space; it does not replace the
original group by an independently chosen elementary group or infer joint
fullness from individual nontrivial characters.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.IndependentCharacterCoordinates

variable (p : ℕ) [Fact p.Prime] {G ι : Type*} [Group G]
    (χ : ι → PrimeCharacters p G)

/-- The simultaneous original character values, with one literal output
coordinate for each original selected character. -/
def joint : G →* (ι → Multiplicative (ZMod p)) where
  toFun g i := Multiplicative.ofAdd (χ i (Additive.ofMul g))
  map_one' := by
    funext i
    apply Multiplicative.toAdd.injective
    exact (χ i).map_zero
  map_mul' g h := by
    funext i
    apply Multiplicative.toAdd.injective
    exact (χ i).map_add (Additive.ofMul g) (Additive.ofMul h)

@[simp] theorem joint_apply (g : G) (i : ι) :
    joint p χ g i = Multiplicative.ofAdd (χ i (Additive.ofMul g)) := rfl

/-- Every prescribed tuple is realized by the same original group element. -/
theorem joint_surjective [Finite G] [Fintype ι]
    (hχ : LinearIndependent (ZMod p) χ) : Function.Surjective (joint p χ) := by
  intro v
  let parameter : (ι → ZMod p) →ₗ[ZMod p] PrimeCharacters p G :=
    Fintype.linearCombination (ZMod p) χ
  have hinj : Function.Injective parameter := hχ.fintypeLinearCombination_injective
  let target : Module.Dual (ZMod p) (ι → ZMod p) :=
    ∑ i, (v i).toAdd • LinearMap.proj i
  obtain ⟨g, hg⟩ := retainedCharacterEvaluation_surjective p parameter hinj
    (Multiplicative.ofAdd target)
  refine ⟨g, ?_⟩
  funext i
  apply Multiplicative.toAdd.injective
  have hi := congrArg
    (fun f : Multiplicative (Module.Dual (ZMod p) (ι → ZMod p)) =>
      f.toAdd (Pi.single i 1)) hg
  change (parameter (Pi.single i 1)) (Additive.ofMul g) = target (Pi.single i 1) at hi
  simpa [parameter, target, Fintype.linearCombination_apply_single,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    Pi.single_apply] using hi

theorem joint_range_eq_top [Finite G] [Fintype ι]
    (hχ : LinearIndependent (ZMod p) χ) : (joint p χ).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (joint_surjective p χ hχ)

/-- In particular, independent original binary characters have full joint
binary image. No transitivity, exponent, or generation premise is needed. -/
theorem binary_joint_surjective [Finite G] [Fintype ι]
    (ψ : ι → PrimeCharacters 2 G) (hψ : LinearIndependent (ZMod 2) ψ) :
    Function.Surjective (joint 2 ψ) := joint_surjective 2 ψ hψ

end SymmetricSubgroupAsymptotics.IndependentCharacterCoordinates
