import SymmetricSubgroupAsymptotics.BinaryCarrierConeData

/-! Exact square certificate for the cone j ≥ 2ell. The two null
directions are removed by a polynomial identity, not by a PSD assumption. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryCarrierCone

def keepA : Fin 7 → Fin 9 := ![0,1,2,3,4,6,7]
def reducedMatrixA : Fin 7 → Fin 7 → ℝ := fun i j => psdA (keepA i) (keepA j)
def reduceA (z : Fin 9 → ℝ) : Fin 7 → ℝ :=
  ![z 0, z 1-(17/44)*z 5, z 2-(21/44)*z 5, z 3, z 4, z 6, z 7-z 8]

/-- Integer linear forms and positive rational coefficients from exact elimination. -/
def squaresA (u : Fin 7 → ℝ) : ℝ :=
  (817*u 0+804*u 1-548*u 2-328*u 3-393*u 4-896*u 5-688*u 6)^2/817 +
  (378102*u 1-8758*u 2+28416*u 3+610*u 4-202009*u 5-146200*u 6)^2/308909334 +
  (5777024*u 2+1328577*u 3+1110928*u 4+8013701*u 5+4213760*u 6)^2/37660419456 +
  (66315703797*u 3+6697251664*u 4-10192648567*u 5-14812335744*u 6)^2/
    11110114959952643712 +
  (17517081717887*u 4-984836712824*u 5-5506161710097*u 6)^2/
    1161657602591238208716939 +
  (63581756789450739*u 5-15871500425430602*u 6)^2/
    2227533658895250353762563336986 +
  (2100371145348629273/63581756789450739)*(u 6)^2

private theorem sum9_scalar (f : Fin 9 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (0))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8
  ring

private theorem sum7_scalar (f : Fin 7 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (0))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6
  ring

private theorem psdA_row0 (z : Fin 9 → ℝ) :
    (∑ j, psdA 0 j * z 0 * z j) =
      (817)*z 0*z 0 + (804)*z 0*z 1 + (-548)*z 0*z 2 + (-328)*z 0*z 3 + (-393)*z 0*z 4 + (-540/11)*z 0*z 5 + (-896)*z 0*z 6 + (-688)*z 0*z 7 + (688)*z 0*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_row1 (z : Fin 9 → ℝ) :
    (∑ j, psdA 1 j * z 1 * z j) =
      (804)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-288)*z 1*z 3 + (-386)*z 1*z 4 + (-222)*z 1*z 5 + (-1129)*z 1*z 6 + (-856)*z 1*z 7 + (856)*z 1*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_row2 (z : Fin 9 → ℝ) :
    (∑ j, psdA 2 j * z 2 * z j) =
      (-548)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (423)*z 2*z 3 + (434)*z 2*z 4 + (-386)*z 2*z 5 + (1836)*z 2*z 6 + (1112)*z 2*z 7 + (-1112)*z 2*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_row3 (z : Fin 9 → ℝ) :
    (∑ j, psdA 3 j * z 3 * z j) =
      (-328)*z 3*z 0 + (-288)*z 3*z 1 + (423)*z 3*z 2 + (577)*z 3*z 3 + (237)*z 3*z 4 + (-3987/44)*z 3*z 5 + (563)*z 3*z 6 + (323)*z 3*z 7 + (-323)*z 3*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_row4 (z : Fin 9 → ℝ) :
    (∑ j, psdA 4 j * z 4 * z j) =
      (-393)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (237)*z 4*z 3 + (490)*z 4*z 4 + (-58)*z 4*z 5 + (646)*z 4*z 6 + (363)*z 4*z 7 + (-363)*z 4*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_row5 (z : Fin 9 → ℝ) :
    (∑ j, psdA 5 j * z 5 * z j) =
      (-540/11)*z 5*z 0 + (-222)*z 5*z 1 + (-386)*z 5*z 2 + (-3987/44)*z 5*z 3 + (-58)*z 5*z 4 + (270)*z 5*z 5 + (-19363/44)*z 5*z 6 + (-200)*z 5*z 7 + (200)*z 5*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_row6 (z : Fin 9 → ℝ) :
    (∑ j, psdA 6 j * z 6 * z j) =
      (-896)*z 6*z 0 + (-1129)*z 6*z 1 + (1836)*z 6*z 2 + (563)*z 6*z 3 + (646)*z 6*z 4 + (-19363/44)*z 6*z 5 + (4645)*z 6*z 6 + (1312)*z 6*z 7 + (-1312)*z 6*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_row7 (z : Fin 9 → ℝ) :
    (∑ j, psdA 7 j * z 7 * z j) =
      (-688)*z 7*z 0 + (-856)*z 7*z 1 + (1112)*z 7*z 2 + (323)*z 7*z 3 + (363)*z 7*z 4 + (-200)*z 7*z 5 + (1312)*z 7*z 6 + (1312)*z 7*z 7 + (-1312)*z 7*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_row8 (z : Fin 9 → ℝ) :
    (∑ j, psdA 8 j * z 8 * z j) =
      (688)*z 8*z 0 + (856)*z 8*z 1 + (-1112)*z 8*z 2 + (-323)*z 8*z 3 + (-363)*z 8*z 4 + (200)*z 8*z 5 + (-1312)*z 8*z 6 + (-1312)*z 8*z 7 + (1312)*z 8*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdA_expansion (z : Fin 9 → ℝ) :
    quadratic psdA z =
      ((817)*z 0*z 0 + (804)*z 0*z 1 + (-548)*z 0*z 2 + (-328)*z 0*z 3 + (-393)*z 0*z 4 + (-540/11)*z 0*z 5 + (-896)*z 0*z 6 + (-688)*z 0*z 7 + (688)*z 0*z 8) +
      ((804)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-288)*z 1*z 3 + (-386)*z 1*z 4 + (-222)*z 1*z 5 + (-1129)*z 1*z 6 + (-856)*z 1*z 7 + (856)*z 1*z 8) +
      ((-548)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (423)*z 2*z 3 + (434)*z 2*z 4 + (-386)*z 2*z 5 + (1836)*z 2*z 6 + (1112)*z 2*z 7 + (-1112)*z 2*z 8) +
      ((-328)*z 3*z 0 + (-288)*z 3*z 1 + (423)*z 3*z 2 + (577)*z 3*z 3 + (237)*z 3*z 4 + (-3987/44)*z 3*z 5 + (563)*z 3*z 6 + (323)*z 3*z 7 + (-323)*z 3*z 8) +
      ((-393)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (237)*z 4*z 3 + (490)*z 4*z 4 + (-58)*z 4*z 5 + (646)*z 4*z 6 + (363)*z 4*z 7 + (-363)*z 4*z 8) +
      ((-540/11)*z 5*z 0 + (-222)*z 5*z 1 + (-386)*z 5*z 2 + (-3987/44)*z 5*z 3 + (-58)*z 5*z 4 + (270)*z 5*z 5 + (-19363/44)*z 5*z 6 + (-200)*z 5*z 7 + (200)*z 5*z 8) +
      ((-896)*z 6*z 0 + (-1129)*z 6*z 1 + (1836)*z 6*z 2 + (563)*z 6*z 3 + (646)*z 6*z 4 + (-19363/44)*z 6*z 5 + (4645)*z 6*z 6 + (1312)*z 6*z 7 + (-1312)*z 6*z 8) +
      ((-688)*z 7*z 0 + (-856)*z 7*z 1 + (1112)*z 7*z 2 + (323)*z 7*z 3 + (363)*z 7*z 4 + (-200)*z 7*z 5 + (1312)*z 7*z 6 + (1312)*z 7*z 7 + (-1312)*z 7*z 8) +
      ((688)*z 8*z 0 + (856)*z 8*z 1 + (-1112)*z 8*z 2 + (-323)*z 8*z 3 + (-363)*z 8*z 4 + (200)*z 8*z 5 + (-1312)*z 8*z 6 + (-1312)*z 8*z 7 + (1312)*z 8*z 8) := by
  unfold quadratic
  rw [sum9_scalar]
  rw [psdA_row0, psdA_row1, psdA_row2, psdA_row3, psdA_row4, psdA_row5, psdA_row6, psdA_row7, psdA_row8]

private theorem reducedMatrixA_row0 (z : Fin 7 → ℝ) :
    (∑ j, reducedMatrixA 0 j * z 0 * z j) =
      (817)*z 0*z 0 + (804)*z 0*z 1 + (-548)*z 0*z 2 + (-328)*z 0*z 3 + (-393)*z 0*z 4 + (-896)*z 0*z 5 + (-688)*z 0*z 6 := by
  rw [sum7_scalar] <;> rfl

private theorem reducedMatrixA_row1 (z : Fin 7 → ℝ) :
    (∑ j, reducedMatrixA 1 j * z 1 * z j) =
      (804)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-288)*z 1*z 3 + (-386)*z 1*z 4 + (-1129)*z 1*z 5 + (-856)*z 1*z 6 := by
  rw [sum7_scalar] <;> rfl

private theorem reducedMatrixA_row2 (z : Fin 7 → ℝ) :
    (∑ j, reducedMatrixA 2 j * z 2 * z j) =
      (-548)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (423)*z 2*z 3 + (434)*z 2*z 4 + (1836)*z 2*z 5 + (1112)*z 2*z 6 := by
  rw [sum7_scalar] <;> rfl

private theorem reducedMatrixA_row3 (z : Fin 7 → ℝ) :
    (∑ j, reducedMatrixA 3 j * z 3 * z j) =
      (-328)*z 3*z 0 + (-288)*z 3*z 1 + (423)*z 3*z 2 + (577)*z 3*z 3 + (237)*z 3*z 4 + (563)*z 3*z 5 + (323)*z 3*z 6 := by
  rw [sum7_scalar] <;> rfl

private theorem reducedMatrixA_row4 (z : Fin 7 → ℝ) :
    (∑ j, reducedMatrixA 4 j * z 4 * z j) =
      (-393)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (237)*z 4*z 3 + (490)*z 4*z 4 + (646)*z 4*z 5 + (363)*z 4*z 6 := by
  rw [sum7_scalar] <;> rfl

private theorem reducedMatrixA_row5 (z : Fin 7 → ℝ) :
    (∑ j, reducedMatrixA 5 j * z 5 * z j) =
      (-896)*z 5*z 0 + (-1129)*z 5*z 1 + (1836)*z 5*z 2 + (563)*z 5*z 3 + (646)*z 5*z 4 + (4645)*z 5*z 5 + (1312)*z 5*z 6 := by
  rw [sum7_scalar] <;> rfl

private theorem reducedMatrixA_row6 (z : Fin 7 → ℝ) :
    (∑ j, reducedMatrixA 6 j * z 6 * z j) =
      (-688)*z 6*z 0 + (-856)*z 6*z 1 + (1112)*z 6*z 2 + (323)*z 6*z 3 + (363)*z 6*z 4 + (1312)*z 6*z 5 + (1312)*z 6*z 6 := by
  rw [sum7_scalar] <;> rfl

private theorem reducedMatrixA_expansion (z : Fin 7 → ℝ) :
    quadratic reducedMatrixA z =
      ((817)*z 0*z 0 + (804)*z 0*z 1 + (-548)*z 0*z 2 + (-328)*z 0*z 3 + (-393)*z 0*z 4 + (-896)*z 0*z 5 + (-688)*z 0*z 6) +
      ((804)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-288)*z 1*z 3 + (-386)*z 1*z 4 + (-1129)*z 1*z 5 + (-856)*z 1*z 6) +
      ((-548)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (423)*z 2*z 3 + (434)*z 2*z 4 + (1836)*z 2*z 5 + (1112)*z 2*z 6) +
      ((-328)*z 3*z 0 + (-288)*z 3*z 1 + (423)*z 3*z 2 + (577)*z 3*z 3 + (237)*z 3*z 4 + (563)*z 3*z 5 + (323)*z 3*z 6) +
      ((-393)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (237)*z 4*z 3 + (490)*z 4*z 4 + (646)*z 4*z 5 + (363)*z 4*z 6) +
      ((-896)*z 5*z 0 + (-1129)*z 5*z 1 + (1836)*z 5*z 2 + (563)*z 5*z 3 + (646)*z 5*z 4 + (4645)*z 5*z 5 + (1312)*z 5*z 6) +
      ((-688)*z 6*z 0 + (-856)*z 6*z 1 + (1112)*z 6*z 2 + (323)*z 6*z 3 + (363)*z 6*z 4 + (1312)*z 6*z 5 + (1312)*z 6*z 6) := by
  unfold quadratic
  rw [sum7_scalar]
  rw [reducedMatrixA_row0, reducedMatrixA_row1, reducedMatrixA_row2, reducedMatrixA_row3, reducedMatrixA_row4, reducedMatrixA_row5, reducedMatrixA_row6]

private theorem matrixA_row0 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 0 j * z 0 * z j) =
      (1049)*z 0*z 0 + (1008)*z 0*z 1 + (-140)*z 0*z 2 + (106)*z 0*z 3 + (-58)*z 0*z 4 + (24)*z 0*z 5 + (-400)*z 0*z 6 + (-528)*z 0*z 7 + (1112)*z 0*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixA_row1 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 1 j * z 1 * z j) =
      (1008)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-222)*z 1*z 3 + (-386)*z 1*z 4 + (-222)*z 1*z 5 + (-1056)*z 1*z 6 + (-856)*z 1*z 7 + (1112)*z 1*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixA_row2 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 2 j * z 2 * z j) =
      (-140)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (598)*z 2*z 3 + (434)*z 2*z 4 + (-386)*z 2*z 5 + (2224)*z 2*z 6 + (1112)*z 2*z 7 + (1112)*z 2*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixA_row3 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 3 j * z 3 * z j) =
      (106)*z 3*z 0 + (-222)*z 3*z 1 + (598)*z 3*z 2 + (762)*z 3*z 3 + (598)*z 3*z 4 + (-58)*z 3*z 5 + (912)*z 3*z 6 + (456)*z 3*z 7 + (1112)*z 3*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixA_row4 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 4 j * z 4 * z j) =
      (-58)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (598)*z 4*z 3 + (598)*z 4*z 4 + (-58)*z 4*z 5 + (912)*z 4*z 6 + (456)*z 4*z 7 + (1112)*z 4*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixA_row5 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 5 j * z 5 * z j) =
      (24)*z 5*z 0 + (-222)*z 5*z 1 + (-386)*z 5*z 2 + (-58)*z 5*z 3 + (-58)*z 5*z 4 + (270)*z 5*z 5 + (-400)*z 5*z 6 + (-200)*z 5*z 7 + (1112)*z 5*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixA_row6 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 6 j * z 6 * z j) =
      (-400)*z 6*z 0 + (-1056)*z 6*z 1 + (2224)*z 6*z 2 + (912)*z 6*z 3 + (912)*z 6*z 4 + (-400)*z 6*z 5 + (5248)*z 6*z 6 + (1312)*z 6*z 7 + (-1312)*z 6*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixA_row7 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 7 j * z 7 * z j) =
      (-528)*z 7*z 0 + (-856)*z 7*z 1 + (1112)*z 7*z 2 + (456)*z 7*z 3 + (456)*z 7*z 4 + (-200)*z 7*z 5 + (1312)*z 7*z 6 + (1312)*z 7*z 7 + (-1312)*z 7*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixA_row8 (z : Fin 9 → ℝ) :
    (∑ j, matrixA 8 j * z 8 * z j) =
      (1112)*z 8*z 0 + (1112)*z 8*z 1 + (1112)*z 8*z 2 + (1112)*z 8*z 3 + (1112)*z 8*z 4 + (1112)*z 8*z 5 + (-1312)*z 8*z 6 + (-1312)*z 8*z 7 + (1312)*z 8*z 8 := by
  rw [sum9_scalar] <;> rfl

theorem matrixA_expansion (z : Fin 9 → ℝ) :
    quadratic matrixA z =
      ((1049)*z 0*z 0 + (1008)*z 0*z 1 + (-140)*z 0*z 2 + (106)*z 0*z 3 + (-58)*z 0*z 4 + (24)*z 0*z 5 + (-400)*z 0*z 6 + (-528)*z 0*z 7 + (1112)*z 0*z 8) +
      ((1008)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-222)*z 1*z 3 + (-386)*z 1*z 4 + (-222)*z 1*z 5 + (-1056)*z 1*z 6 + (-856)*z 1*z 7 + (1112)*z 1*z 8) +
      ((-140)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (598)*z 2*z 3 + (434)*z 2*z 4 + (-386)*z 2*z 5 + (2224)*z 2*z 6 + (1112)*z 2*z 7 + (1112)*z 2*z 8) +
      ((106)*z 3*z 0 + (-222)*z 3*z 1 + (598)*z 3*z 2 + (762)*z 3*z 3 + (598)*z 3*z 4 + (-58)*z 3*z 5 + (912)*z 3*z 6 + (456)*z 3*z 7 + (1112)*z 3*z 8) +
      ((-58)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (598)*z 4*z 3 + (598)*z 4*z 4 + (-58)*z 4*z 5 + (912)*z 4*z 6 + (456)*z 4*z 7 + (1112)*z 4*z 8) +
      ((24)*z 5*z 0 + (-222)*z 5*z 1 + (-386)*z 5*z 2 + (-58)*z 5*z 3 + (-58)*z 5*z 4 + (270)*z 5*z 5 + (-400)*z 5*z 6 + (-200)*z 5*z 7 + (1112)*z 5*z 8) +
      ((-400)*z 6*z 0 + (-1056)*z 6*z 1 + (2224)*z 6*z 2 + (912)*z 6*z 3 + (912)*z 6*z 4 + (-400)*z 6*z 5 + (5248)*z 6*z 6 + (1312)*z 6*z 7 + (-1312)*z 6*z 8) +
      ((-528)*z 7*z 0 + (-856)*z 7*z 1 + (1112)*z 7*z 2 + (456)*z 7*z 3 + (456)*z 7*z 4 + (-200)*z 7*z 5 + (1312)*z 7*z 6 + (1312)*z 7*z 7 + (-1312)*z 7*z 8) +
      ((1112)*z 8*z 0 + (1112)*z 8*z 1 + (1112)*z 8*z 2 + (1112)*z 8*z 3 + (1112)*z 8*z 4 + (1112)*z 8*z 5 + (-1312)*z 8*z 6 + (-1312)*z 8*z 7 + (1312)*z 8*z 8) := by
  unfold quadratic
  rw [sum9_scalar]
  rw [matrixA_row0, matrixA_row1, matrixA_row2, matrixA_row3, matrixA_row4, matrixA_row5, matrixA_row6, matrixA_row7, matrixA_row8]

theorem kernel_reductionA (z : Fin 9 → ℝ) :
    quadratic psdA z = quadratic reducedMatrixA (reduceA z) := by
  have h0 : reduceA z 0 = z 0 := rfl
  have h1 : reduceA z 1 = z 1-(17/44)*z 5 := rfl
  have h2 : reduceA z 2 = z 2-(21/44)*z 5 := rfl
  have h3 : reduceA z 3 = z 3 := rfl
  have h4 : reduceA z 4 = z 4 := rfl
  have h5 : reduceA z 5 = z 6 := rfl
  have h6 : reduceA z 6 = z 7-z 8 := rfl
  rw [psdA_expansion, reducedMatrixA_expansion]
  simp only [h0, h1, h2, h3, h4, h5, h6]
  ring

theorem square_identityA (u : Fin 7 → ℝ) :
    quadratic reducedMatrixA u = squaresA u := by
  rw [reducedMatrixA_expansion]
  unfold squaresA
  ring

theorem psdA_nonneg (z : Fin 9 → ℝ) : 0 ≤ quadratic psdA z := by
  rw [kernel_reductionA, square_identityA]
  unfold squaresA
  positivity

theorem remainderA_nonneg (i j : Fin 9) : 0 ≤ matrixA i j - psdA i j := by
  fin_cases i <;> fin_cases j <;> norm_num [matrixA, psdA]

/-- The whole cone matrix is nonnegative on every nonnegative real vector. -/
theorem matrixA_nonneg (z : Fin 9 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ quadratic matrixA z := by
  have h := quadratic_nonneg (fun i j => matrixA i j-psdA i j) z remainderA_nonneg hz
  rw [quadratic_sub] at h
  exact (psdA_nonneg z).trans (sub_nonneg.mp h)

end SymmetricSubgroupAsymptotics.BinaryCarrierCone
