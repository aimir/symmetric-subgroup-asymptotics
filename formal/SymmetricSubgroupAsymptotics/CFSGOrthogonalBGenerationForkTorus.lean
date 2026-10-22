import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationLongElements
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationForkTorus
import SymmetricSubgroupAsymptotics.CFSGMatrixIdentityExtension
import Mathlib.Algebra.Group.Units.Hom

/-! The genuine long fork torus in odd-characteristic B. Its defining
D-shaped sparse word is lifted only after every one of its long-root
factors is proved to be an actual B short-root commutator. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationForkTorus
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBGenerationLongElements
open CFSGOrthogonalBGenerationShortCommutator CFSGOrthogonalBGenerationShortArrays
open CFSGMatrixIdentityExtension
variable (K : Type) [Field K]

abbrev pen := CFSGOrthogonalDGenerationForkTorus.pen
abbrev last := CFSGOrthogonalDGenerationForkTorus.last

def extendUnit (s : ℕ) : (CFSGOrthogonalDSerreMatrices.Mat K (s + 2))ˣ →*
    (Mat K (s + 2))ˣ := Units.map (extend K (Fin (s + 2) ⊕ Fin (s + 2)) Unit)

private theorem previous_last (s : ℕ) :
    CFSGOrthogonalDSerreMatrices.previous (s + 2) (last s) = pen s := by
  apply Fin.ext
  dsimp [CFSGOrthogonalDSerreMatrices.previous, last, pen,
    CFSGOrthogonalDGenerationForkTorus.last, CFSGOrthogonalDGenerationForkTorus.pen]

private theorem positive_block (s : ℕ) (a : K) :
    1 + a • longArray K (s + 2) (Sum.inl (pen s)) (Sum.inl (last s)) =
      (extendUnit K s (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) false (last s) a) :
        Mat K (s + 2)) := by
  have hi : ¬ (last s).val + 1 < s + 2 := by
    dsimp [last, CFSGOrthogonalDGenerationForkTorus.last]
    omega
  change _ = extend K (Fin (s + 2) ⊕ Fin (s + 2)) Unit
    (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) false (last s) a :
      CFSGOrthogonalDSerreMatrices.Mat K (s + 2))
  rw [CFSGOrthogonalDSerreMatrices.rootTransvection_val]
  ext x y
  rcases x with ((x | x) | ⟨⟩) <;> rcases y with ((y | y) | ⟨⟩) <;>
    simp [extend, Matrix.fromBlocks, longArray, paired,
      CFSGOrthogonalDSerreMatrices.rootMatrix, CFSGOrthogonalDSerreMatrices.positive,
      hi, previous_last, Matrix.single_apply, Matrix.one_apply]

private theorem negative_block (s : ℕ) (a : K) :
    1 + a • longArray K (s + 2) (Sum.inr (last s)) (Sum.inr (pen s)) =
      (extendUnit K s (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) true (last s) a) :
        Mat K (s + 2)) := by
  have hi : ¬ (last s).val + 1 < s + 2 := by
    dsimp [last, CFSGOrthogonalDGenerationForkTorus.last]
    omega
  change _ = extend K (Fin (s + 2) ⊕ Fin (s + 2)) Unit
    (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) true (last s) a :
      CFSGOrthogonalDSerreMatrices.Mat K (s + 2))
  rw [CFSGOrthogonalDSerreMatrices.rootTransvection_val]
  ext x y
  rcases x with ((x | x) | ⟨⟩) <;> rcases y with ((y | y) | ⟨⟩) <;>
    simp [extend, Matrix.fromBlocks, longArray, paired,
      CFSGOrthogonalDSerreMatrices.rootMatrix, CFSGOrthogonalDSerreMatrices.negative,
      CFSGOrthogonalDSerreMatrices.positive, hi, previous_last,
      Matrix.transpose_apply, Matrix.single_apply, Matrix.one_apply]

theorem extended_positive_mem (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) :
    extendUnit K s (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) false (last s) a) ∈
      elementaryRootGroup K (s + 2) := by
  let u := longRootElement K (s + 1) (Sum.inl (pen s)) (Sum.inl (last s)) a
  have hu : (u.val : Mat K (s + 2)) =
      1 + a • longArray K (s + 2) (Sum.inl (pen s)) (Sum.inl (last s)) :=
    longRootElement_val K h2 (s + 1) _ _
      (fun he => CFSGOrthogonalDGenerationForkTorus.pen_ne_last s (Sum.inl.inj he))
      (by intro he; cases he) a
  have he : u.val = extendUnit K s
      (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) false (last s) a) :=
    Units.ext (hu.trans (positive_block K s a))
  exact he ▸ u.property

theorem extended_negative_mem (h2 : (2 : K) ≠ 0) (s : ℕ) (a : K) :
    extendUnit K s (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) true (last s) a) ∈
      elementaryRootGroup K (s + 2) := by
  let u := longRootElement K (s + 1) (Sum.inr (last s)) (Sum.inr (pen s)) a
  have hu : (u.val : Mat K (s + 2)) =
      1 + a • longArray K (s + 2) (Sum.inr (last s)) (Sum.inr (pen s)) :=
    longRootElement_val K h2 (s + 1) _ _
      (fun he => (CFSGOrthogonalDGenerationForkTorus.pen_ne_last s).symm (Sum.inr.inj he))
      (by intro he; cases he) a
  have he : u.val = extendUnit K s
      (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) true (last s) a) :=
    Units.ext (hu.trans (negative_block K s a))
  exact he ▸ u.property

def forkTorus (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) : elementaryRootGroup K (s + 2) :=
  ⟨extendUnit K s (CFSGOrthogonalDGenerationForkTorus.forkTorus K s g).val, by
    change extendUnit K s
      (CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) false (last s) ((g : K) - 1) *
        CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) true (last s) 1 *
        CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) false (last s) ((g : K)⁻¹ - 1) *
        CFSGOrthogonalDSerreMatrices.rootTransvection K (s + 2) true (last s) (-(g : K))) ∈ _
    simp only [map_mul]
    exact (elementaryRootGroup K (s + 2)).mul_mem
      ((elementaryRootGroup K (s + 2)).mul_mem
        ((elementaryRootGroup K (s + 2)).mul_mem
          (extended_positive_mem K h2 s _) (extended_negative_mem K h2 s _))
        (extended_positive_mem K h2 s _)) (extended_negative_mem K h2 s _)⟩

def forkDiagonal (s : ℕ) (g : Kˣ) : Index (s + 2) → K :=
  Sum.elim (CFSGOrthogonalDGenerationForkTorus.forkDiagonal K s g) (fun _ => 1)

theorem forkTorus_val (h2 : (2 : K) ≠ 0) (s : ℕ) (g : Kˣ) :
    ((forkTorus K h2 s g).val : Mat K (s + 2)) = Matrix.diagonal (forkDiagonal K s g) := by
  change extend K (Fin (s + 2) ⊕ Fin (s + 2)) Unit
    ((CFSGOrthogonalDGenerationForkTorus.forkTorus K s g).val :
      CFSGOrthogonalDSerreMatrices.Mat K (s + 2)) = _
  rw [CFSGOrthogonalDGenerationForkTorus.forkTorus_coe]
  ext x y
  cases x <;> cases y <;>
    simp [extend, Matrix.fromBlocks, forkDiagonal, Matrix.diagonal_apply, Matrix.one_apply]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationForkTorus
