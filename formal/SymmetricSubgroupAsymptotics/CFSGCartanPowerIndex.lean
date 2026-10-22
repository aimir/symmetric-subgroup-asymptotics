import SymmetricSubgroupAsymptotics.CFSGIntegerMatrixPowerHom

/-! A checked integer Smith certificate with a single nontrivial diagonal
factor bounds the index of the literal monomial image over any finite field.
Only a right inverse for the change of variables is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCartanPowerIndex
open CFSGIntegerMatrixPowerHom

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Concrete integral changes of variables reducing an exponent matrix to
one nontrivial Smith factor. No abstract Smith theorem is assumed. -/
structure OneFactorCertificate (A : Matrix I I ℤ) (i : I) (d : ℕ) where
  left : Matrix I I ℤ
  right : Matrix I I ℤ
  rightInv : Matrix I I ℤ
  right_inverse : right * rightInv = 1
  diagonalization : left * A * right = Matrix.diagonal (fun j => if j = i then (d : ℤ) else 1)

variable {A : Matrix I I ℤ} {i : I} {d : ℕ}
variable (S : OneFactorCertificate A i d)
variable {G : Type*} [CommGroup G]

/-- The changed coordinates of an actual kernel element obey the diagonal
power equations. -/
theorem kernel_coordinate (x : (powerHom A : (I → G) →* (I → G)).ker) (j : I) :
    (powerHom S.rightInv x.val j) ^ (if j = i then (d : ℤ) else 1) = 1 := by
  have hrv := powerHom_rightInverse S.right S.rightInv S.right_inverse x.val
  have hx : powerHom A x.val = 1 := x.property
  have h : powerHom (Matrix.diagonal (fun j => if j = i then (d : ℤ) else 1))
      (powerHom S.rightInv x.val) = 1 := by
    rw [← S.diagonalization, powerHom_mul, powerHom_mul, hrv, hx, map_one]
  simpa only [powerHom_diagonal, Pi.one_apply] using congrFun h j

variable (K : Type*) [Field K]

/-- All coordinates except the distinguished one are forced to be one;
the remaining coordinate is a literal root of unity. -/
def kernelRoot (x : (powerHom A : (I → Kˣ) →* (I → Kˣ)).ker) : rootsOfUnity d K :=
  ⟨powerHom S.rightInv x.val i, (mem_rootsOfUnity d _).mpr (by
    simpa only [ite_true, zpow_natCast] using kernel_coordinate S x i)⟩

theorem kernelRoot_injective : Function.Injective (kernelRoot S K) := by
  intro x y hxy
  have he : powerHom S.rightInv x.val = powerHom S.rightInv y.val := by
    funext j
    by_cases hji : j = i
    · subst j
      exact congrArg Subtype.val hxy
    · have hx := kernel_coordinate S x j
      have hy := kernel_coordinate S y j
      simp only [if_neg hji, zpow_one] at hx hy
      exact hx.trans hy.symm
  apply Subtype.ext
  calc
    x.val = powerHom S.right (powerHom S.rightInv x.val) :=
      (powerHom_rightInverse S.right S.rightInv S.right_inverse x.val).symm
    _ = powerHom S.right (powerHom S.rightInv y.val) := congrArg (powerHom S.right) he
    _ = y.val := powerHom_rightInverse S.right S.rightInv S.right_inverse y.val

include S

/-- The actual image index, not just a determinant or a formal cokernel,
is bounded by the distinguished Smith factor. -/
theorem range_index_le [Finite K] [NeZero d] :
    (powerHom A : (I → Kˣ) →* (I → Kˣ)).range.index ≤ d := by
  rw [Subgroup.index_range]
  calc
    Nat.card (powerHom A : (I → Kˣ) →* (I → Kˣ)).ker ≤ Nat.card (rootsOfUnity d K) :=
      Nat.card_le_card_of_injective (kernelRoot S K) (kernelRoot_injective S K)
    _ = Fintype.card (rootsOfUnity d K) := Nat.card_eq_fintype_card
    _ ≤ d := card_rootsOfUnity (R := K) (k := d)

end SymmetricSubgroupAsymptotics.CFSGCartanPowerIndex
