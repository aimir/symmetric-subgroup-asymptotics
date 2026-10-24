import SymmetricSubgroupAsymptotics.CFSGHeisenbergKernelRigidity
import SymmetricSubgroupAsymptotics.CFSGSymplecticFullGroup
import SymmetricSubgroupAsymptotics.CFSGSymplecticElementaryProjectiveCenter
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.LinearAlgebra.Matrix.Notation

/-! A literal three-coordinate Heisenberg group inside the SAME
elementary C2 matrices. Its central parameter is the long-root entry
minus twice the original central coordinate. The central quotient map
is injective when two is nonzero; no claim is made in characteristic two.
Membership uses the proved equality of the original elementary group
with the actual form-preserving matrices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergEmbedding

open CFSGHeisenbergCoordinateGroup CFSGSymplecticSerreMatrices
open CFSGSymplecticStabilizerCoordinates
variable (K : Type) [Field K]

def matrix (a b c : K) : Mat K 2 :=
  Matrix.fromBlocks !![1, a; 0, 1] !![a * b - 2 * c, b; b, 0]
    0 !![1, 0; -a, 1]

theorem matrix_zero : matrix K 0 0 0 = 1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.one_apply]

theorem matrix_mul (a b c a' b' c' : K) :
    matrix K a b c * matrix K a' b' c' =
      matrix K (a + a') (b + b') (c + c' + b * a') := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

def matrixHom : Element K 1 →* Mat K 2 where
  toFun g := matrix K (g.a 0) (g.b 0) g.c
  map_one' := matrix_zero K
  map_mul' g h := by
    change matrix K (g.a 0 + h.a 0) (g.b 0 + h.b 0)
        (g.c + h.c + dot g.b h.a) = _
    rw [matrix_mul]
    simp only [dot, Fin.sum_univ_one]

theorem matrix_preserves_pairing (a b c : K) : PreservesPairing 2 (matrix K a b c) := by
  intro v w
  simp [CFSGSymplecticTransvectionGeometry.pairing, matrix, Matrix.mulVec,
    dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

def elementaryHom : Element K 1 →* elementaryRootGroup K 2 where
  toFun g := ⟨(matrixHom K).toHomUnits g,
    all_formPreserving_elementary K 2 _
      (matrix_preserves_pairing K (g.a 0) (g.b 0) g.c)⟩
  map_one' := Subtype.ext ((matrixHom K).toHomUnits.map_one)
  map_mul' g h := Subtype.ext ((matrixHom K).toHomUnits.map_mul g h)

theorem elementaryHom_val (g : Element K 1) :
    ((elementaryHom K g).val : Mat K 2) = matrix K (g.a 0) (g.b 0) g.c := rfl

theorem central_matrix (z : Multiplicative K) :
    ((elementaryHom K (central z)).val : Mat K 2) =
      1 + Matrix.single (Sum.inl (0 : Fin 2)) (Sum.inr (0 : Fin 2)) (-2 * z.toAdd) := by
  rw [elementaryHom_val]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [matrix, central, Matrix.single_apply, Matrix.one_apply] <;> ring

def projectiveHom : Element K 1 →* elementaryProjective K 2 :=
  (QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K 2))).comp (elementaryHom K)

theorem projective_central_injective (hTwo : (2 : K) ≠ 0) :
    Function.Injective ((projectiveHom K).comp (central (K := K) (m := 1))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro z hz
  apply Subgroup.mem_bot.mpr
  have hc : elementaryHom K (central z) ∈ Subgroup.center (elementaryRootGroup K 2) :=
    (QuotientGroup.eq_one_iff _).mp hz
  obtain ⟨s, hs⟩ := (elementaryRootGroup_center_iff_scalar K 1 _).mp hc
  rw [central_matrix] at hs
  have h02 := congrArg (fun A : Mat K 2 => A (Sum.inl 0) (Sum.inr 0)) hs
  have hz0 : (2 : K) * z.toAdd = 0 := by
    simpa [Matrix.single_apply, Matrix.one_apply] using h02
  have he : z.toAdd = 0 := (mul_eq_zero.mp hz0).resolve_left hTwo
  exact congrArg Multiplicative.ofAdd he

theorem projectiveHom_injective (hTwo : (2 : K) ≠ 0) :
    Function.Injective (projectiveHom K) :=
  CFSGHeisenbergKernelRigidity.injective_of_central (projectiveHom K)
    (projective_central_injective K hTwo)

end SymmetricSubgroupAsymptotics.CFSGSymplecticHeisenbergEmbedding
