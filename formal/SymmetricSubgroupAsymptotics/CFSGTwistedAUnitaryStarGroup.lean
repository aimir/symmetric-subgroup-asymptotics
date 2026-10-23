import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarSecondAxis
import SymmetricSubgroupAsymptotics.CFSGTwoPlaneShearArrays

/-! The full literal two-plane shear subgroup of the SAME natural fixed
group. Its four base-field dimensions are actual parameters: two central
trace-kernel coordinates and one unrestricted quadratic-field coordinate.
Membership comes from displayed actual radical and conjugated-root words.
No unitary recognition or assumed root-star equality is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryNaturalRadical CFSGSerreOrdinaryTwists

abbrev StarParameters (q : CFSG.PrimePower) (s : ℕ) :=
  centralParameters q (s + 1) × (q.Extension 2 × centralParameters q (s + 1))

def starCoefficient (q : CFSG.PrimePower) (s : ℕ) (x : StarParameters q s) :
    Matrix (Fin 2) (Fin 2) (q.Extension 2) :=
  !![x.1.val, parity q (s + 1) * definingFieldAutomorphism q 2 x.2.1;
      x.2.1, x.2.2.val]

theorem starCoefficient_zero (q : CFSG.PrimePower) (s : ℕ) :
    starCoefficient q s 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · change parity q (s + 1) * definingFieldAutomorphism q 2 0 = 0
    rw [map_zero, mul_zero]
  · rfl
  · rfl

theorem starCoefficient_add (q : CFSG.PrimePower) (s : ℕ) (x y : StarParameters q s) :
    starCoefficient q s (x + y) = starCoefficient q s x + starCoefficient q s y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [starCoefficient, map_add, mul_add]

theorem starCoefficient_injective (q : CFSG.PrimePower) (s : ℕ) :
    Function.Injective (starCoefficient q s) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (q.Extension 2) => M 0 0) h
    exact he
  · apply Prod.ext
    · have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (q.Extension 2) => M 1 0) h
      exact he
    · apply Subtype.ext
      have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) (q.Extension 2) => M 1 1) h
      exact he

def starFixed (q : CFSG.PrimePower) (s : ℕ) (x : StarParameters q s) : naturalFixed (s + 3) q :=
  starRadicalFixed q s x.2.1 x.1 * starSecondAxisFixed q s x.2.2

theorem starFixed_matrix (q : CFSG.PrimePower) (s : ℕ) (x : StarParameters q s) :
    ((starFixed q s x).val.val : Mat (q.Extension 2) (s + 3)) =
      (CFSGTwoPlaneShearArrays.unit (starPositive s) (starNegative s)
        (star_coordinates_disjoint s) (starCoefficient q s x) : Mat (q.Extension 2) (s + 3)) := by
  let A : Matrix (Fin 2) (Fin 2) (q.Extension 2) :=
    !![x.1.val, parity q (s + 1) * definingFieldAutomorphism q 2 x.2.1; x.2.1, 0]
  let C : Matrix (Fin 2) (Fin 2) (q.Extension 2) := !![0, 0; 0, x.2.2.val]
  have hA : ((starRadicalFixed q s x.2.1 x.1).val.val : Mat (q.Extension 2) (s + 3)) =
      (CFSGTwoPlaneShearArrays.unit (starPositive s) (starNegative s)
        (star_coordinates_disjoint s) A : Mat (q.Extension 2) (s + 3)) := by
    rw [starRadicalFixed_matrix]
    change _ = 1 + CFSGTwoPlaneShearArrays.array (starPositive s) (starNegative s) A
    simp only [CFSGTwoPlaneShearArrays.array, Fin.sum_univ_two, A, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.single_zero, add_zero]
    abel
  have hC : ((starSecondAxisFixed q s x.2.2).val.val : Mat (q.Extension 2) (s + 3)) =
      (CFSGTwoPlaneShearArrays.unit (starPositive s) (starNegative s)
        (star_coordinates_disjoint s) C : Mat (q.Extension 2) (s + 3)) := by
    rw [starSecondAxisFixed_matrix]
    change _ = 1 + CFSGTwoPlaneShearArrays.array (starPositive s) (starNegative s) C
    simp only [CFSGTwoPlaneShearArrays.array, Fin.sum_univ_two, C, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.single_zero, zero_add, add_zero]
  have hsum : A + C = starCoefficient q s x := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, C, starCoefficient]
  change ((starRadicalFixed q s x.2.1 x.1).val.val : Mat (q.Extension 2) (s + 3)) *
    ((starSecondAxisFixed q s x.2.2).val.val : Mat (q.Extension 2) (s + 3)) = _
  rw [hA, hC, ← Units.val_mul, ← CFSGTwoPlaneShearArrays.unit_add, hsum]

theorem starFixed_zero (q : CFSG.PrimePower) (s : ℕ) : starFixed q s 0 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [starFixed_matrix, starCoefficient_zero, CFSGTwoPlaneShearArrays.unit_zero]
  rfl

theorem starFixed_add (q : CFSG.PrimePower) (s : ℕ) (x y : StarParameters q s) :
    starFixed q s (x + y) = starFixed q s x * starFixed q s y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change ((starFixed q s (x + y)).val.val : Mat (q.Extension 2) (s + 3)) =
    ((starFixed q s x).val.val : Mat (q.Extension 2) (s + 3)) *
      ((starFixed q s y).val.val : Mat (q.Extension 2) (s + 3))
  rw [starFixed_matrix, starFixed_matrix, starFixed_matrix, starCoefficient_add,
    CFSGTwoPlaneShearArrays.unit_add]
  rfl

theorem starFixed_injective (q : CFSG.PrimePower) (s : ℕ) : Function.Injective (starFixed q s) := by
  intro x y h
  apply starCoefficient_injective q s
  apply CFSGTwoPlaneShearArrays.unit_injective (starPositive s) (starNegative s)
    (starPositive_injective s) (starNegative_injective s) (star_coordinates_disjoint s)
  apply Units.ext
  have he := congrArg (fun g : naturalFixed (s + 3) q => (g.val.val : Mat (q.Extension 2) (s + 3))) h
  simpa only [starFixed_matrix] using he

def starParameterHom (q : CFSG.PrimePower) (s : ℕ) :
    Multiplicative (StarParameters q s) →* naturalFixed (s + 3) q where
  toFun x := starFixed q s x.toAdd
  map_one' := starFixed_zero q s
  map_mul' x y := starFixed_add q s x.toAdd y.toAdd

def naturalRootStarGroup (q : CFSG.PrimePower) (s : ℕ) : Subgroup (naturalFixed (s + 3) q) :=
  (starParameterHom q s).range

theorem naturalRootStarGroup_allCommute (q : CFSG.PrimePower) (s : ℕ) :
    ∀ x ∈ naturalRootStarGroup q s, ∀ y ∈ naturalRootStarGroup q s, Commute x y := by
  rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
  change starParameterHom q s a * starParameterHom q s b =
    starParameterHom q s b * starParameterHom q s a
  rw [← map_mul, ← map_mul, mul_comm a b]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
