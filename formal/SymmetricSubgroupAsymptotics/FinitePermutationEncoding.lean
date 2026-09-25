import SymmetricSubgroupAsymptotics.FiniteCayleyReflection
import Mathlib.Algebra.BigOperators.Fin

/-!
# Compact faithful permutation codes

A permutation on n original points is encoded by its n base-n image digits.
Composition on the right is a permutation of those digits. All row checks
therefore use finite natural-number arithmetic, while the reflection theorem
retains the actual original permutation generators and group operation.
-/

set_option autoImplicit false

namespace SymmetricSubgroupAsymptotics

/-- The literal base-n image code of a permutation. -/
def permutationCode {n : ℕ} (g : Equiv.Perm (Fin n)) : Fin (n^n) :=
  finFunctionFinEquiv (fun x => g x)

theorem permutationCode_injective (n : ℕ) :
    Function.Injective (@permutationCode n) := by
  intro g h he
  have hf := finFunctionFinEquiv.injective he
  exact Equiv.ext (congrFun hf)

/-- The faithful encoding needed by the reflected finite Cayley checker. -/
def permutationGeneratorEncoding {n : ℕ} {ι : Type*}
    (generators : ι → Equiv.Perm (Fin n)) :
    GeneratorEncoding generators (Fin (n^n)) where
  encode := permutationCode
  injective := permutationCode_injective n
  one := permutationCode 1
  encode_one := rfl
  step c j := finFunctionFinEquiv (fun x => finFunctionFinEquiv.symm c (generators j x))
  encode_step g j := by
    change finFunctionFinEquiv (fun x => g (generators j x)) = _
    congr 1
    funext x
    simp only [permutationCode, Equiv.symm_apply_apply]

/-- The encoding uses the exact original zero-based image rows. -/
theorem permutationCode_val {n : ℕ} (g : Equiv.Perm (Fin n)) :
    (permutationCode g).val = ∑ i : Fin n, (g i).val * n ^ i.val := rfl

/-- Explicit numeric transition formula, useful for independent exporters. -/
theorem permutationGeneratorEncoding_step_val {n : ℕ} {ι : Type*}
    (generators : ι → Equiv.Perm (Fin n)) (c : Fin (n^n)) (j : ι) :
    ((permutationGeneratorEncoding generators).step c j).val =
      ∑ i : Fin n, (c.val / n ^ (generators j i).val % n) * n ^ i.val := rfl

end SymmetricSubgroupAsymptotics
