import SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Tactic.Abel

/-! A faithful upper-triangular matrix action is soluble. The proof is
uniform in the dimension: deleting the first row and column gives the
smaller faithful image, while the kernel of the diagonal-and-tail map is
the abelian group of first-row shears. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
universe u
namespace SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
open Matrix

def tailMatrix {F : Type u} {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) :
    Matrix (Fin n) (Fin n) F := A.submatrix Fin.succ Fin.succ

theorem upper_tail_mul {F : Type u} [Field F] {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F} (hA : A.BlockTriangular id) :
    tailMatrix (A * B) = tailMatrix A * tailMatrix B := by
  ext i j
  change (∑ k : Fin (n + 1), A i.succ k * B k j.succ) =
    ∑ k : Fin n, A i.succ k.succ * B k.succ j.succ
  rw [Fin.sum_univ_succ]
  have hzero : A i.succ 0 = 0 := hA (by change 0 < i.val + 1; omega)
  rw [hzero, zero_mul, zero_add]

theorem tail_kernel_row {F : Type u} [Field F] {n : ℕ}
    {A : Matrix (Fin (n + 1)) (Fin (n + 1)) F}
    (hA : A.BlockTriangular id) (ht : tailMatrix A = 1) (i : Fin n)
    (j : Fin (n + 1)) : A i.succ j = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i.succ j := by
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [hA (by change 0 < i.val + 1; omega)]
    simp [Fin.succ_ne_zero]
  · have h := congrArg (fun M : Matrix (Fin n) (Fin n) F => M i j) ht
    change A i.succ j.succ = (1 : Matrix (Fin n) (Fin n) F) i j at h
    simpa only [Matrix.one_apply, Fin.succ_inj] using h

theorem shear_difference_mul_zero {F : Type u} [Field F] {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F}
    (hA : A.BlockTriangular id) (hA0 : A 0 0 = 1)
    (hB : B.BlockTriangular id) (htB : tailMatrix B = 1) :
    (A - 1) * (B - 1) = 0 := by
  have hc (i : Fin (n + 1)) : (A - 1) i 0 = 0 := by
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Matrix.sub_apply, hA0, Matrix.one_apply_eq, sub_self]
    · rw [Matrix.sub_apply, hA (by change 0 < i.val + 1; omega)]
      simp [Fin.succ_ne_zero]
  ext i j
  change (∑ k : Fin (n + 1), (A - 1) i k * (B - 1) k j) = 0
  apply Finset.sum_eq_zero
  intro k _
  refine Fin.cases ?_ (fun k => ?_) k
  · rw [hc i, zero_mul]
  · have hr : (B - 1) k.succ j = 0 := by
      rw [Matrix.sub_apply, tail_kernel_row hB htB, sub_self]
    rw [hr, mul_zero]

theorem first_row_shears_commute {F : Type u} [Field F] {n : ℕ}
    {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) F}
    (hA : A.BlockTriangular id) (hA0 : A 0 0 = 1) (htA : tailMatrix A = 1)
    (hB : B.BlockTriangular id) (hB0 : B 0 0 = 1) (htB : tailMatrix B = 1) :
    A * B = B * A := by
  have hab : A * B - B = A - 1 := sub_eq_zero.mp (by
    simpa only [sub_mul, mul_sub, mul_one, one_mul] using
      shear_difference_mul_zero hA hA0 hB htB)
  have hba : B * A - A = B - 1 := sub_eq_zero.mp (by
    simpa only [sub_mul, mul_sub, mul_one, one_mul] using
      shear_difference_mul_zero hB hB0 hA htA)
  calc
    A * B = (A - 1) + B := sub_eq_iff_eq_add.mp hab
    _ = (B - 1) + A := by abel
    _ = B * A := (sub_eq_iff_eq_add.mp hba).symm

def upperTailHom {F : Type u} [Field F] {n : ℕ} {G : Type u} [Group G]
    (rho : G →* Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hupper : ∀ g, (rho g).BlockTriangular id) : G →* Matrix (Fin n) (Fin n) F where
  toFun := fun g => tailMatrix (rho g)
  map_one' := by
    ext i j
    simp only [tailMatrix, Matrix.submatrix_apply, rho.map_one, Matrix.one_apply, Fin.succ_inj]
  map_mul' := fun g h => by rw [rho.map_mul]; exact upper_tail_mul (hupper g)

def upperFirstDiagonalHom {F : Type u} [Field F] {n : ℕ} {G : Type u} [Group G]
    (rho : G →* Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (hupper : ∀ g, (rho g).BlockTriangular id) : G →* F where
  toFun := fun g => rho g 0 0
  map_one' := by rw [rho.map_one]; exact Matrix.one_apply_eq 0
  map_mul' := fun g h => by rw [rho.map_mul]; exact upper_diag_mul (hupper g) (hupper h) 0

theorem soluble_of_faithful_upper_matrix (F : Type u) [Field F] :
    ∀ (n : ℕ) (G : Type u) [Group G] (rho : G →* Matrix (Fin n) (Fin n) F),
      Function.Injective rho → (∀ g, (rho g).BlockTriangular id) → IsSolvable G := by
  intro n
  induction n with
  | zero =>
    intro G _ rho hinj _
    letI upperSoluble_zero : Subsingleton G := ⟨fun x y => hinj (Subsingleton.elim _ _)⟩
    infer_instance
  | succ n ih =>
    intro G _ rho hinj hupper
    let t := (upperTailHom rho hupper).toHomUnits
    let Q := t.range
    let rhoQ : Q →* Matrix (Fin n) (Fin n) F := (Units.coeHom _).comp Q.subtype
    have hQinj : Function.Injective rhoQ := by
      intro x y h
      apply Subtype.ext
      apply Units.ext
      exact h
    have hQupper (q : Q) : (rhoQ q).BlockTriangular id := by
      obtain ⟨g, hg⟩ := q.property
      have hm : rhoQ q = tailMatrix (rho g) := by
        have hval := congrArg (fun z : (Matrix (Fin n) (Fin n) F)ˣ => z.val) hg.symm
        exact hval
      rw [hm]
      intro i j hij
      exact hupper g (by change j.val + 1 < i.val + 1; change j.val < i.val at hij; omega)
    letI upperSoluble_tail : IsSolvable Q := ih Q rhoQ hQinj hQupper
    let f : G →* Fˣ × Q := (upperFirstDiagonalHom rho hupper).toHomUnits.prod t.rangeRestrict
    have hker : IsSolvable f.ker := by
      apply isSolvable_of_comm
      intro x y
      have hdiag (z : f.ker) : rho z.val 0 0 = 1 := by
        have h := congrArg (fun w : Fˣ × Q => (w.1 : F)) (MonoidHom.mem_ker.mp z.property)
        exact h
      have htail (z : f.ker) : tailMatrix (rho z.val) = 1 := by
        have h := congrArg (fun w : Fˣ × Q => ((w.2 : (Matrix (Fin n) (Fin n) F)ˣ) :
          Matrix (Fin n) (Fin n) F)) (MonoidHom.mem_ker.mp z.property)
        exact h
      apply Subtype.ext
      apply hinj
      change rho (x.val * y.val) = rho (y.val * x.val)
      rw [rho.map_mul, rho.map_mul]
      exact first_row_shears_commute (hupper x.val) (hdiag x) (htail x)
        (hupper y.val) (hdiag y) (htail y)
    letI upperSoluble_kernel : IsSolvable f.ker := hker
    apply solvable_of_ker_le_range f.ker.subtype f
    rw [Subgroup.range_subtype]

theorem borel_soluble (F : Type u) [Field F] (n : ℕ) : IsSolvable (borel F n) := by
  let rho : borel F n →* Matrix (Fin n) (Fin n) F :=
    { toFun := fun g => g.val.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply soluble_of_faithful_upper_matrix F n (borel F n) rho
  · intro x y h
    exact Subtype.ext (Subtype.ext h)
  · intro g
    exact g.property

end SymmetricSubgroupAsymptotics.CFSGUpperUnitriangular
