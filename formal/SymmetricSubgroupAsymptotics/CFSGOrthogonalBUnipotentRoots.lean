import SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationSLChain
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationLongElements

/-! Actual chain, quadratic short and skew long roots in the SAME
natural B unipotent subgroup. Every membership is proved from its
original root word and actual flag coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationSLChain
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationShortMembership
open CFSGOrthogonalBGenerationLongElements CFSGOrthogonalBGenerationShortCommutator
variable (K : Type) [Field K]

private theorem single_diag_zero {I : Type*} [DecidableEq I] (i j : I) (hij : i ≠ j)
    (a : K) (x : I) : Matrix.single i j a x x = 0 := by
  rw [Matrix.single_apply]
  apply if_neg
  rintro ⟨hi, hj⟩
  exact hij (hi.trans hj.symm)

def chainElement (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : K) : elementaryRootGroup K n :=
  doubleIntoElementary K n (CFSGTypeAElementaryMatrices.elementary hij a)

theorem chainElement_val (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : K) :
    ((chainElement K n i j hij a).val : Mat K n) =
      1 + a • (Matrix.single (pos n i) (pos n j) 1 - Matrix.single (neg n j) (neg n i) 1) :=
  doubleHom_elementary_val K n i j hij a

theorem chainElement_mem_unipotent (n : ℕ) (i j : Fin n) (hij : i < j) (a : K) :
    chainElement K n i j (ne_of_lt hij) a ∈ unipotent K n := by
  have hp : flagEquiv n (pos n i) ≤ flagEquiv n (pos n j) := by
    change i.val ≤ j.val
    exact hij.le
  have hn : flagEquiv n (neg n j) ≤ flagEquiv n (neg n i) :=
    ((flag_neg_lt_neg n j i).mpr hij).le
  refine ⟨?_, ?_⟩
  · change ((chainElement K n i j (ne_of_lt hij) a).val : Mat K n).BlockTriangular (flagEquiv n)
    rw [chainElement_val]
    simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.blockTriangular_one.add
      ((Matrix.blockTriangular_single hp a).sub (Matrix.blockTriangular_single hn a))
  · intro x
    change ((chainElement K n i j (ne_of_lt hij) a).val : Mat K n) x x = 1
    rw [chainElement_val]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      single_diag_zero K (pos n i) (pos n j) (by simpa [pos] using ne_of_lt hij) 1 x,
      single_diag_zero K (neg n j) (neg n i) (by simpa [neg] using ne_of_gt hij) 1 x,
      Matrix.one_apply_eq, sub_self, smul_zero, add_zero]

def chainInU (n : ℕ) (i j : Fin n) (hij : i < j) (a : K) : unipotent K n :=
  ⟨chainElement K n i j (ne_of_lt hij) a, chainElement_mem_unipotent K n i j hij a⟩

def shortElement (s : ℕ) (i : Fin (s + 1)) (a : K) : elementaryRootGroup K (s + 1) :=
  ⟨shortUnit K (s + 1) (Sum.inl i) a, shortUnit_mem K s (Sum.inl i) a⟩

theorem shortElement_val (s : ℕ) (i : Fin (s + 1)) (a : K) :
    ((shortElement K s i a).val : Mat K (s + 1)) =
      1 + a • (Matrix.single (pos (s + 1) i) (middle (s + 1)) 1 -
        Matrix.single (middle (s + 1)) (neg (s + 1) i) 2) +
      a ^ 2 • Matrix.single (pos (s + 1) i) (neg (s + 1) i) (-1) := rfl

theorem shortElement_mem_unipotent (s : ℕ) (i : Fin (s + 1)) (a : K) :
    shortElement K s i a ∈ unipotent K (s + 1) := by
  have hp := (flag_pos_lt_middle (s + 1) i).le
  have hn := (flag_middle_lt_neg (s + 1) i).le
  have hpn := (flag_pos_lt_neg (s + 1) i i).le
  refine ⟨?_, ?_⟩
  · change ((shortElement K s i a).val : Mat K (s + 1)).BlockTriangular (flagEquiv (s + 1))
    rw [shortElement_val]
    simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
    exact (Matrix.blockTriangular_one.add
      ((Matrix.blockTriangular_single hp a).sub (Matrix.blockTriangular_single hn (a * 2)))).add
      (Matrix.blockTriangular_single hpn (a ^ 2 * (-1)))
  · intro x
    change ((shortElement K s i a).val : Mat K (s + 1)) x x = 1
    rw [shortElement_val]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      single_diag_zero K (pos (s + 1) i) (middle (s + 1)) (by simp [pos, middle]) 1 x,
      single_diag_zero K (middle (s + 1)) (neg (s + 1) i) (by simp [middle, neg]) 2 x,
      single_diag_zero K (pos (s + 1) i) (neg (s + 1) i) (by simp [pos, neg]) (-1) x,
      Matrix.one_apply_eq, sub_self, smul_zero, add_zero]

def shortInU (s : ℕ) (i : Fin (s + 1)) (a : K) : unipotent K (s + 1) :=
  ⟨shortElement K s i a, shortElement_mem_unipotent K s i a⟩

def skewElement (s : ℕ) (i j : Fin (s + 1)) (a : K) : elementaryRootGroup K (s + 1) :=
  longRootElement K s (Sum.inl i) (Sum.inl j) a

theorem skewElement_val (h2 : (2 : K) ≠ 0) (s : ℕ)
    (i j : Fin (s + 1)) (hij : i ≠ j) (a : K) :
    ((skewElement K s i j a).val : Mat K (s + 1)) =
      1 + a • (Matrix.single (pos (s + 1) i) (neg (s + 1) j) 1 -
        Matrix.single (pos (s + 1) j) (neg (s + 1) i) 1) :=
  longRootElement_val K h2 s _ _ (by simpa using hij) (by intro h; cases h) a

theorem skewElement_mem_unipotent (h2 : (2 : K) ≠ 0) (s : ℕ)
    (i j : Fin (s + 1)) (hij : i ≠ j) (a : K) :
    skewElement K s i j a ∈ unipotent K (s + 1) := by
  refine ⟨?_, ?_⟩
  · change ((skewElement K s i j a).val : Mat K (s + 1)).BlockTriangular (flagEquiv (s + 1))
    rw [skewElement_val K h2 s i j hij a]
    simp only [smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
    exact Matrix.blockTriangular_one.add
      ((Matrix.blockTriangular_single (flag_pos_lt_neg _ i j).le a).sub
        (Matrix.blockTriangular_single (flag_pos_lt_neg _ j i).le a))
  · intro x
    change ((skewElement K s i j a).val : Mat K (s + 1)) x x = 1
    rw [skewElement_val K h2 s i j hij a]
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,
      single_diag_zero K (pos (s + 1) i) (neg (s + 1) j) (by simp [pos, neg]) 1 x,
      single_diag_zero K (pos (s + 1) j) (neg (s + 1) i) (by simp [pos, neg]) 1 x,
      Matrix.one_apply_eq, sub_self, smul_zero, add_zero]

def skewInU (h2 : (2 : K) ≠ 0) (s : ℕ) (i j : Fin (s + 1)) (hij : i ≠ j)
    (a : K) : unipotent K (s + 1) :=
  ⟨skewElement K s i j a, skewElement_mem_unipotent K h2 s i j hij a⟩

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBUnipotent
