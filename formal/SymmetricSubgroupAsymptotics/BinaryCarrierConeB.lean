import SymmetricSubgroupAsymptotics.BinaryCarrierConeData

/-! Exact square certificate for the cone j ≤ 2ell, including j < ell.
The original rational matrix is retained with its full third coordinate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryCarrierCone

def keepB : Fin 8 → Fin 9 := ![0,1,2,3,4,6,7,8]
def reducedMatrixB : Fin 8 → Fin 8 → ℝ := fun i j => psdB (keepB i) (keepB j)
def reduceB (z : Fin 9 → ℝ) : Fin 8 → ℝ :=
  ![z 0, z 1-(17/44)*z 5, z 2-(21/44)*z 5, z 3, z 4, z 6, z 7, z 8]

def squaresB (u : Fin 8 → ℝ) : ℝ :=
  (729*u 0+721*u 1-469*u 2-236*u 3-318*u 4-416*u 5-480*u 6+86*u 7)^2/729 +
  (394325*u 1-62801*u 2-45628*u 3-52116*u 4-111949*u 5-80385*u 6-63464*u 7)^2/
    287462925 +
  (370093856*u 2+106941693*u 3+85974696*u 4+246417844*u 5+245913685*u 6-144140341*u 7)^2/
    145937259767200 +
  (140632346331*u 3+24714761784*u 4-21470817140*u 5-56015120093*u 6+24941506013*u 7)^2/
    52047167331967242336 +
  (12115482713145*u 4-1581429530473*u 5-5214186791734*u 6+1597637257204*u 7)^2/
    567942920294083722073665 +
  (9880284507591032*u 5-16211804730781444*u 6-9641231845292351*u 7)^2/
    179556624229010260085145773460 +
  (451040479314224047*u 6+54079410165854913*u 7)^2/
    557051032508095149108873036993313 +
  (333948094921809911021/1804161917256896188)*(u 7)^2

private theorem sum9_scalar (f : Fin 9 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (0))))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8
  ring

private theorem sum8_scalar (f : Fin 8 → ℝ) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (0)))))))) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7
  ring

private theorem psdB_row0 (z : Fin 9 → ℝ) :
    (∑ j, psdB 0 j * z 0 * z j) =
      (729)*z 0*z 0 + (721)*z 0*z 1 + (-469)*z 0*z 2 + (-236)*z 0*z 3 + (-318)*z 0*z 4 + (-602/11)*z 0*z 5 + (-416)*z 0*z 6 + (-480)*z 0*z 7 + (86)*z 0*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_row1 (z : Fin 9 → ℝ) :
    (∑ j, psdB 1 j * z 1 * z j) =
      (721)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-296)*z 1*z 3 + (-386)*z 1*z 4 + (-222)*z 1*z 5 + (-565)*z 1*z 6 + (-585)*z 1*z 7 + (-2)*z 1*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_row2 (z : Fin 9 → ℝ) :
    (∑ j, psdB 2 j * z 2 * z j) =
      (-469)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (433)*z 2*z 3 + (434)*z 2*z 4 + (-386)*z 2*z 5 + (917)*z 2*z 6 + (950)*z 2*z 7 + (-407)*z 2*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_row3 (z : Fin 9 → ℝ) :
    (∑ j, psdB 3 j * z 3 * z j) =
      (-236)*z 3*z 0 + (-296)*z 3*z 1 + (433)*z 3*z 2 + (542)*z 3*z 3 + (241)*z 3*z 4 + (-4061/44)*z 3*z 5 + (275)*z 3*z 6 + (197)*z 3*z 7 + (-56)*z 3*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_row4 (z : Fin 9 → ℝ) :
    (∑ j, psdB 4 j * z 4 * z j) =
      (-318)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (241)*z 4*z 3 + (469)*z 4*z 4 + (-58)*z 4*z 5 + (303)*z 4*z 6 + (231)*z 4*z 7 + (-65)*z 4*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_row5 (z : Fin 9 → ℝ) :
    (∑ j, psdB 5 j * z 5 * z j) =
      (-602/11)*z 5*z 0 + (-222)*z 5*z 1 + (-386)*z 5*z 2 + (-4061/44)*z 5*z 3 + (-58)*z 5*z 4 + (270)*z 5*z 5 + (-2413/11)*z 5*z 6 + (-10005/44)*z 5*z 7 + (8581/44)*z 5*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_row6 (z : Fin 9 → ℝ) :
    (∑ j, psdB 6 j * z 6 * z j) =
      (-416)*z 6*z 0 + (-565)*z 6*z 1 + (917)*z 6*z 2 + (275)*z 6*z 3 + (303)*z 6*z 4 + (-2413/11)*z 6*z 5 + (1254)*z 6*z 6 + (-134)*z 6*z 7 + (-813)*z 6*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_row7 (z : Fin 9 → ℝ) :
    (∑ j, psdB 7 j * z 7 * z j) =
      (-480)*z 7*z 0 + (-585)*z 7*z 1 + (950)*z 7*z 2 + (197)*z 7*z 3 + (231)*z 7*z 4 + (-10005/44)*z 7*z 5 + (-134)*z 7*z 6 + (2690)*z 7*z 7 + (591)*z 7*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_row8 (z : Fin 9 → ℝ) :
    (∑ j, psdB 8 j * z 8 * z j) =
      (86)*z 8*z 0 + (-2)*z 8*z 1 + (-407)*z 8*z 2 + (-56)*z 8*z 3 + (-65)*z 8*z 4 + (8581/44)*z 8*z 5 + (-813)*z 8*z 6 + (591)*z 8*z 7 + (891)*z 8*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem psdB_expansion (z : Fin 9 → ℝ) :
    quadratic psdB z =
      ((729)*z 0*z 0 + (721)*z 0*z 1 + (-469)*z 0*z 2 + (-236)*z 0*z 3 + (-318)*z 0*z 4 + (-602/11)*z 0*z 5 + (-416)*z 0*z 6 + (-480)*z 0*z 7 + (86)*z 0*z 8) +
      ((721)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-296)*z 1*z 3 + (-386)*z 1*z 4 + (-222)*z 1*z 5 + (-565)*z 1*z 6 + (-585)*z 1*z 7 + (-2)*z 1*z 8) +
      ((-469)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (433)*z 2*z 3 + (434)*z 2*z 4 + (-386)*z 2*z 5 + (917)*z 2*z 6 + (950)*z 2*z 7 + (-407)*z 2*z 8) +
      ((-236)*z 3*z 0 + (-296)*z 3*z 1 + (433)*z 3*z 2 + (542)*z 3*z 3 + (241)*z 3*z 4 + (-4061/44)*z 3*z 5 + (275)*z 3*z 6 + (197)*z 3*z 7 + (-56)*z 3*z 8) +
      ((-318)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (241)*z 4*z 3 + (469)*z 4*z 4 + (-58)*z 4*z 5 + (303)*z 4*z 6 + (231)*z 4*z 7 + (-65)*z 4*z 8) +
      ((-602/11)*z 5*z 0 + (-222)*z 5*z 1 + (-386)*z 5*z 2 + (-4061/44)*z 5*z 3 + (-58)*z 5*z 4 + (270)*z 5*z 5 + (-2413/11)*z 5*z 6 + (-10005/44)*z 5*z 7 + (8581/44)*z 5*z 8) +
      ((-416)*z 6*z 0 + (-565)*z 6*z 1 + (917)*z 6*z 2 + (275)*z 6*z 3 + (303)*z 6*z 4 + (-2413/11)*z 6*z 5 + (1254)*z 6*z 6 + (-134)*z 6*z 7 + (-813)*z 6*z 8) +
      ((-480)*z 7*z 0 + (-585)*z 7*z 1 + (950)*z 7*z 2 + (197)*z 7*z 3 + (231)*z 7*z 4 + (-10005/44)*z 7*z 5 + (-134)*z 7*z 6 + (2690)*z 7*z 7 + (591)*z 7*z 8) +
      ((86)*z 8*z 0 + (-2)*z 8*z 1 + (-407)*z 8*z 2 + (-56)*z 8*z 3 + (-65)*z 8*z 4 + (8581/44)*z 8*z 5 + (-813)*z 8*z 6 + (591)*z 8*z 7 + (891)*z 8*z 8) := by
  unfold quadratic
  rw [sum9_scalar]
  rw [psdB_row0, psdB_row1, psdB_row2, psdB_row3, psdB_row4, psdB_row5, psdB_row6, psdB_row7, psdB_row8]

private theorem reducedMatrixB_row0 (z : Fin 8 → ℝ) :
    (∑ j, reducedMatrixB 0 j * z 0 * z j) =
      (729)*z 0*z 0 + (721)*z 0*z 1 + (-469)*z 0*z 2 + (-236)*z 0*z 3 + (-318)*z 0*z 4 + (-416)*z 0*z 5 + (-480)*z 0*z 6 + (86)*z 0*z 7 := by
  rw [sum8_scalar] <;> rfl

private theorem reducedMatrixB_row1 (z : Fin 8 → ℝ) :
    (∑ j, reducedMatrixB 1 j * z 1 * z j) =
      (721)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-296)*z 1*z 3 + (-386)*z 1*z 4 + (-565)*z 1*z 5 + (-585)*z 1*z 6 + (-2)*z 1*z 7 := by
  rw [sum8_scalar] <;> rfl

private theorem reducedMatrixB_row2 (z : Fin 8 → ℝ) :
    (∑ j, reducedMatrixB 2 j * z 2 * z j) =
      (-469)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (433)*z 2*z 3 + (434)*z 2*z 4 + (917)*z 2*z 5 + (950)*z 2*z 6 + (-407)*z 2*z 7 := by
  rw [sum8_scalar] <;> rfl

private theorem reducedMatrixB_row3 (z : Fin 8 → ℝ) :
    (∑ j, reducedMatrixB 3 j * z 3 * z j) =
      (-236)*z 3*z 0 + (-296)*z 3*z 1 + (433)*z 3*z 2 + (542)*z 3*z 3 + (241)*z 3*z 4 + (275)*z 3*z 5 + (197)*z 3*z 6 + (-56)*z 3*z 7 := by
  rw [sum8_scalar] <;> rfl

private theorem reducedMatrixB_row4 (z : Fin 8 → ℝ) :
    (∑ j, reducedMatrixB 4 j * z 4 * z j) =
      (-318)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (241)*z 4*z 3 + (469)*z 4*z 4 + (303)*z 4*z 5 + (231)*z 4*z 6 + (-65)*z 4*z 7 := by
  rw [sum8_scalar] <;> rfl

private theorem reducedMatrixB_row5 (z : Fin 8 → ℝ) :
    (∑ j, reducedMatrixB 5 j * z 5 * z j) =
      (-416)*z 5*z 0 + (-565)*z 5*z 1 + (917)*z 5*z 2 + (275)*z 5*z 3 + (303)*z 5*z 4 + (1254)*z 5*z 5 + (-134)*z 5*z 6 + (-813)*z 5*z 7 := by
  rw [sum8_scalar] <;> rfl

private theorem reducedMatrixB_row6 (z : Fin 8 → ℝ) :
    (∑ j, reducedMatrixB 6 j * z 6 * z j) =
      (-480)*z 6*z 0 + (-585)*z 6*z 1 + (950)*z 6*z 2 + (197)*z 6*z 3 + (231)*z 6*z 4 + (-134)*z 6*z 5 + (2690)*z 6*z 6 + (591)*z 6*z 7 := by
  rw [sum8_scalar] <;> rfl

private theorem reducedMatrixB_row7 (z : Fin 8 → ℝ) :
    (∑ j, reducedMatrixB 7 j * z 7 * z j) =
      (86)*z 7*z 0 + (-2)*z 7*z 1 + (-407)*z 7*z 2 + (-56)*z 7*z 3 + (-65)*z 7*z 4 + (-813)*z 7*z 5 + (591)*z 7*z 6 + (891)*z 7*z 7 := by
  rw [sum8_scalar] <;> rfl

private theorem reducedMatrixB_expansion (z : Fin 8 → ℝ) :
    quadratic reducedMatrixB z =
      ((729)*z 0*z 0 + (721)*z 0*z 1 + (-469)*z 0*z 2 + (-236)*z 0*z 3 + (-318)*z 0*z 4 + (-416)*z 0*z 5 + (-480)*z 0*z 6 + (86)*z 0*z 7) +
      ((721)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-296)*z 1*z 3 + (-386)*z 1*z 4 + (-565)*z 1*z 5 + (-585)*z 1*z 6 + (-2)*z 1*z 7) +
      ((-469)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (433)*z 2*z 3 + (434)*z 2*z 4 + (917)*z 2*z 5 + (950)*z 2*z 6 + (-407)*z 2*z 7) +
      ((-236)*z 3*z 0 + (-296)*z 3*z 1 + (433)*z 3*z 2 + (542)*z 3*z 3 + (241)*z 3*z 4 + (275)*z 3*z 5 + (197)*z 3*z 6 + (-56)*z 3*z 7) +
      ((-318)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (241)*z 4*z 3 + (469)*z 4*z 4 + (303)*z 4*z 5 + (231)*z 4*z 6 + (-65)*z 4*z 7) +
      ((-416)*z 5*z 0 + (-565)*z 5*z 1 + (917)*z 5*z 2 + (275)*z 5*z 3 + (303)*z 5*z 4 + (1254)*z 5*z 5 + (-134)*z 5*z 6 + (-813)*z 5*z 7) +
      ((-480)*z 6*z 0 + (-585)*z 6*z 1 + (950)*z 6*z 2 + (197)*z 6*z 3 + (231)*z 6*z 4 + (-134)*z 6*z 5 + (2690)*z 6*z 6 + (591)*z 6*z 7) +
      ((86)*z 7*z 0 + (-2)*z 7*z 1 + (-407)*z 7*z 2 + (-56)*z 7*z 3 + (-65)*z 7*z 4 + (-813)*z 7*z 5 + (591)*z 7*z 6 + (891)*z 7*z 7) := by
  unfold quadratic
  rw [sum8_scalar]
  rw [reducedMatrixB_row0, reducedMatrixB_row1, reducedMatrixB_row2, reducedMatrixB_row3, reducedMatrixB_row4, reducedMatrixB_row5, reducedMatrixB_row6, reducedMatrixB_row7]

private theorem matrixB_row0 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 0 j * z 0 * z j) =
      (1049)*z 0*z 0 + (1008)*z 0*z 1 + (-140)*z 0*z 2 + (106)*z 0*z 3 + (-58)*z 0*z 4 + (24)*z 0*z 5 + (-200)*z 0*z 6 + (-200)*z 0*z 7 + (1112)*z 0*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixB_row1 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 1 j * z 1 * z j) =
      (1008)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-222)*z 1*z 3 + (-386)*z 1*z 4 + (-222)*z 1*z 5 + (-528)*z 1*z 6 + (-528)*z 1*z 7 + (1112)*z 1*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixB_row2 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 2 j * z 2 * z j) =
      (-140)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (598)*z 2*z 3 + (434)*z 2*z 4 + (-386)*z 2*z 5 + (1112)*z 2*z 6 + (1112)*z 2*z 7 + (1112)*z 2*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixB_row3 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 3 j * z 3 * z j) =
      (106)*z 3*z 0 + (-222)*z 3*z 1 + (598)*z 3*z 2 + (762)*z 3*z 3 + (598)*z 3*z 4 + (-58)*z 3*z 5 + (456)*z 3*z 6 + (456)*z 3*z 7 + (1112)*z 3*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixB_row4 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 4 j * z 4 * z j) =
      (-58)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (598)*z 4*z 3 + (598)*z 4*z 4 + (-58)*z 4*z 5 + (456)*z 4*z 6 + (456)*z 4*z 7 + (1112)*z 4*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixB_row5 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 5 j * z 5 * z j) =
      (24)*z 5*z 0 + (-222)*z 5*z 1 + (-386)*z 5*z 2 + (-58)*z 5*z 3 + (-58)*z 5*z 4 + (270)*z 5*z 5 + (-200)*z 5*z 6 + (-200)*z 5*z 7 + (1112)*z 5*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixB_row6 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 6 j * z 6 * z j) =
      (-200)*z 6*z 0 + (-528)*z 6*z 1 + (1112)*z 6*z 2 + (456)*z 6*z 3 + (456)*z 6*z 4 + (-200)*z 6*z 5 + (1312)*z 6*z 6 + (0)*z 6*z 7 + (-656)*z 6*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixB_row7 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 7 j * z 7 * z j) =
      (-200)*z 7*z 0 + (-528)*z 7*z 1 + (1112)*z 7*z 2 + (456)*z 7*z 3 + (456)*z 7*z 4 + (-200)*z 7*z 5 + (0)*z 7*z 6 + (3936)*z 7*z 7 + (1968)*z 7*z 8 := by
  rw [sum9_scalar] <;> rfl

private theorem matrixB_row8 (z : Fin 9 → ℝ) :
    (∑ j, matrixB 8 j * z 8 * z j) =
      (1112)*z 8*z 0 + (1112)*z 8*z 1 + (1112)*z 8*z 2 + (1112)*z 8*z 3 + (1112)*z 8*z 4 + (1112)*z 8*z 5 + (-656)*z 8*z 6 + (1968)*z 8*z 7 + (1312)*z 8*z 8 := by
  rw [sum9_scalar] <;> rfl

theorem matrixB_expansion (z : Fin 9 → ℝ) :
    quadratic matrixB z =
      ((1049)*z 0*z 0 + (1008)*z 0*z 1 + (-140)*z 0*z 2 + (106)*z 0*z 3 + (-58)*z 0*z 4 + (24)*z 0*z 5 + (-200)*z 0*z 6 + (-200)*z 0*z 7 + (1112)*z 0*z 8) +
      ((1008)*z 1*z 0 + (1254)*z 1*z 1 + (-550)*z 1*z 2 + (-222)*z 1*z 3 + (-386)*z 1*z 4 + (-222)*z 1*z 5 + (-528)*z 1*z 6 + (-528)*z 1*z 7 + (1112)*z 1*z 8) +
      ((-140)*z 2*z 0 + (-550)*z 2*z 1 + (1254)*z 2*z 2 + (598)*z 2*z 3 + (434)*z 2*z 4 + (-386)*z 2*z 5 + (1112)*z 2*z 6 + (1112)*z 2*z 7 + (1112)*z 2*z 8) +
      ((106)*z 3*z 0 + (-222)*z 3*z 1 + (598)*z 3*z 2 + (762)*z 3*z 3 + (598)*z 3*z 4 + (-58)*z 3*z 5 + (456)*z 3*z 6 + (456)*z 3*z 7 + (1112)*z 3*z 8) +
      ((-58)*z 4*z 0 + (-386)*z 4*z 1 + (434)*z 4*z 2 + (598)*z 4*z 3 + (598)*z 4*z 4 + (-58)*z 4*z 5 + (456)*z 4*z 6 + (456)*z 4*z 7 + (1112)*z 4*z 8) +
      ((24)*z 5*z 0 + (-222)*z 5*z 1 + (-386)*z 5*z 2 + (-58)*z 5*z 3 + (-58)*z 5*z 4 + (270)*z 5*z 5 + (-200)*z 5*z 6 + (-200)*z 5*z 7 + (1112)*z 5*z 8) +
      ((-200)*z 6*z 0 + (-528)*z 6*z 1 + (1112)*z 6*z 2 + (456)*z 6*z 3 + (456)*z 6*z 4 + (-200)*z 6*z 5 + (1312)*z 6*z 6 + (0)*z 6*z 7 + (-656)*z 6*z 8) +
      ((-200)*z 7*z 0 + (-528)*z 7*z 1 + (1112)*z 7*z 2 + (456)*z 7*z 3 + (456)*z 7*z 4 + (-200)*z 7*z 5 + (0)*z 7*z 6 + (3936)*z 7*z 7 + (1968)*z 7*z 8) +
      ((1112)*z 8*z 0 + (1112)*z 8*z 1 + (1112)*z 8*z 2 + (1112)*z 8*z 3 + (1112)*z 8*z 4 + (1112)*z 8*z 5 + (-656)*z 8*z 6 + (1968)*z 8*z 7 + (1312)*z 8*z 8) := by
  unfold quadratic
  rw [sum9_scalar]
  rw [matrixB_row0, matrixB_row1, matrixB_row2, matrixB_row3, matrixB_row4, matrixB_row5, matrixB_row6, matrixB_row7, matrixB_row8]

theorem kernel_reductionB (z : Fin 9 → ℝ) :
    quadratic psdB z = quadratic reducedMatrixB (reduceB z) := by
  have h0 : reduceB z 0 = z 0 := rfl
  have h1 : reduceB z 1 = z 1-(17/44)*z 5 := rfl
  have h2 : reduceB z 2 = z 2-(21/44)*z 5 := rfl
  have h3 : reduceB z 3 = z 3 := rfl
  have h4 : reduceB z 4 = z 4 := rfl
  have h5 : reduceB z 5 = z 6 := rfl
  have h6 : reduceB z 6 = z 7 := rfl
  have h7 : reduceB z 7 = z 8 := rfl
  rw [psdB_expansion, reducedMatrixB_expansion]
  simp only [h0, h1, h2, h3, h4, h5, h6, h7]
  ring

theorem square_identityB (u : Fin 8 → ℝ) :
    quadratic reducedMatrixB u = squaresB u := by
  rw [reducedMatrixB_expansion]
  unfold squaresB
  ring

theorem psdB_nonneg (z : Fin 9 → ℝ) : 0 ≤ quadratic psdB z := by
  rw [kernel_reductionB, square_identityB]
  unfold squaresB
  positivity

theorem remainderB_nonneg (i j : Fin 9) : 0 ≤ matrixB i j - psdB i j := by
  fin_cases i <;> fin_cases j <;> norm_num [matrixB, psdB]

theorem matrixB_nonneg (z : Fin 9 → ℝ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ quadratic matrixB z := by
  have h := quadratic_nonneg (fun i j => matrixB i j-psdB i j) z remainderB_nonneg hz
  rw [quadratic_sub] at h
  exact (psdB_nonneg z).trans (sub_nonneg.mp h)

end SymmetricSubgroupAsymptotics.BinaryCarrierCone
