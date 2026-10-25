import SymmetricSubgroupAsymptotics.QuaternaryBinaryMatrixEmbedding
import Mathlib.LinearAlgebra.SymplecticGroup
import Mathlib.Algebra.CharP.Two

/-! The literal F4 unitary group embeds faithfully into the standard
binary symplectic group by scalar restriction in (1,omega). The proof
is uniform in the actual finite coordinate type. No group order,
splitting, natural-group recognition, or model embedding is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.QuaternaryUnitarySymplecticEmbedding
open QuaternaryBinaryMatrixEmbedding

def squaring : K →+* K where
  toFun z := z^2
  map_zero' := by decide +kernel
  map_one' := by decide +kernel
  map_add' := by exact (by decide +kernel : ∀ z w : K, (z+w)^2=z^2+w^2)
  map_mul' := by exact (by decide +kernel : ∀ z w : K, (z*w)^2=z^2*w^2)

private theorem square_square : ∀ z : K, squaring (squaring z)=z := by decide +kernel
private theorem square_coordinates : ∀ z : K, (z^2).re=z.re+z.im ∧ (z^2).im=z.im := by
  decide +kernel

variable (I : Type*) [Fintype I] [DecidableEq I]

def adjoint (A : Matrix I I K) : Matrix I I K := squaring.mapMatrix A.transpose

theorem adjoint_mul (A C : Matrix I I K) : adjoint I (A*C)=adjoint I C*adjoint I A := by
  change squaring.mapMatrix (A*C).transpose=_
  rw [Matrix.transpose_mul,map_mul]
  rfl

theorem adjoint_involutive (A : Matrix I I K) : adjoint I (adjoint I A)=A := by
  funext i j
  exact square_square (A i j)

private theorem split_as_blocks (A : Matrix I I K) :
    splitMatrixHom I A=Matrix.fromBlocks (A.map (fun z => z.re)) (A.map (fun z => z.im))
      (A.map (fun z => z.im)) (A.map (fun z => z.re)+A.map (fun z => z.im)) := by
  funext i j
  cases i <;> cases j <;> rfl

private theorem binary_matrix_neg {J : Type*} (M : Matrix J J B) : -M=M := by
  funext i j
  exact CharTwo.neg_eq (M i j)

private theorem binary_matrix_add_self {J : Type*} (M : Matrix J J B) : M+M=0 := by
  funext i j
  exact CharTwo.add_self_eq_zero (M i j)

variable [Nonempty I]

theorem adjoint_binary (A : Matrix I I K) :
    splitMatrixHom I (adjoint I A)=Matrix.J I B*(splitMatrixHom I A).transpose*Matrix.J I B := by
  have hr : (adjoint I A).map (fun z => z.re)=
      (A.map (fun z => z.re)).transpose+(A.map (fun z => z.im)).transpose := by
    funext i j
    exact (square_coordinates (A j i)).1
  have hi : (adjoint I A).map (fun z => z.im)=(A.map (fun z => z.im)).transpose := by
    funext i j
    exact (square_coordinates (A j i)).2
  rw [split_as_blocks,hr,hi,split_as_blocks,Matrix.J,binary_matrix_neg (1:Matrix I I B)]
  simp only [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,Matrix.transpose_add,
    Matrix.zero_mul,Matrix.mul_zero,Matrix.one_mul,Matrix.mul_one,zero_add,add_zero,
    add_assoc,binary_matrix_add_self]

theorem symplectic_of_unitary (A : Matrix I I K) (hA : adjoint I A*A=1) :
    splitMatrixHom I A ∈ Matrix.symplecticGroup I B := by
  have hh : splitMatrixHom I (adjoint I A)*splitMatrixHom I A=1 := by
    rw [←map_mul,hA,map_one]
  rw [adjoint_binary] at hh
  have hJ : Matrix.J I B*Matrix.J I B=1 := by
    simpa only [binary_matrix_neg] using Matrix.J_squared I B
  apply _root_.SymplecticGroup.mem_iff'.mpr
  have he := congrArg (fun M : Matrix (I⊕I) (I⊕I) B => Matrix.J I B*M) hh
  simpa only [←Matrix.mul_assoc,hJ,Matrix.one_mul,Matrix.mul_one] using he

/-- The ACTUAL unitary subgroup of the displayed matrix-unit group. -/
def unitary : Subgroup (Matrix I I K)ˣ where
  carrier := {A | adjoint I A.val*A.val=1}
  one_mem' := by simp [adjoint]
  mul_mem' := by
    intro A C hA hC
    change adjoint I (A.val*C.val)*(A.val*C.val)=1
    rw [adjoint_mul]
    calc
      (adjoint I C.val*adjoint I A.val)*(A.val*C.val)=
          adjoint I C.val*(adjoint I A.val*A.val)*C.val := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hA,Matrix.mul_one,hC]
  inv_mem' := by
    intro A hA
    have he : adjoint I A.val=A.inv := by
      calc
        adjoint I A.val=(adjoint I A.val*A.val)*A.inv := by
          rw [Matrix.mul_assoc,A.val_inv,Matrix.mul_one]
        _ = A.inv := by rw [hA,Matrix.one_mul]
    have hi : adjoint I A.inv=A.val := by rw [←he,adjoint_involutive]
    change adjoint I A.inv*A.inv=1
    rw [hi]
    exact A.val_inv

def symplecticHom : unitary I →* Matrix.symplecticGroup I B where
  toFun A := ⟨splitMatrixHom I A.val.val,symplectic_of_unitary I A.val.val A.property⟩
  map_one' := Subtype.ext (map_one (splitMatrixHom I))
  map_mul' A C := Subtype.ext (map_mul (splitMatrixHom I) A.val.val C.val.val)

theorem symplecticHom_injective : Function.Injective (symplecticHom I) := by
  intro A C he
  apply Subtype.ext
  apply Units.ext
  exact splitMatrixHom_injective I (congrArg Subtype.val he)

end SymmetricSubgroupAsymptotics.QuaternaryUnitarySymplecticEmbedding
