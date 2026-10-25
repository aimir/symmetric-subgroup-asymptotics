import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareBracketRootRelations
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareSelectedWordTransport
import Mathlib.Tactic.Group

/-! Literal canonical E6 word values of the three sides of the proposed
middle-square relation. The equalities use checked integral root transport,
not the separate finite-matrix diagnostic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareRootWordValues
open CFSGReeFFourMiddleSquareBracketRootData CFSGReeFFourMiddleSquareBracketRootRelations
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGFFourE6PositiveRootUnits
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateWordRootElementSign
local notation "A" => CartanMatrix.E₆
private def w : List (Fin 6) := [0,5,1,2,4,3,2,4,3]
private def v : List (Fin 6) := [2,4,3,2,4,3,0,5,1]

variable (K : Type) [CommRing K] [CharP K 2]

private abbrev C (i : Fin 6) := canonicalRoot e6Data K false i 1
private abbrev W (s : List (Fin 6)) := canonicalWord e6Data K s

private theorem word_append (s t : List (Fin 6)) :
    canonicalWord e6Data K (s++t) = canonicalWord e6Data K s*canonicalWord e6Data K t := by
  induction s with
  | nil => simp only [List.nil_append,canonicalWord,one_mul]
  | cons i s ih => rw [List.cons_append,canonicalWord,ih,canonicalWord,mul_assoc]

def yWord := C K 2*C K 4*C K 3*(W K [2,4]*C K 3*(W K [2,4])⁻¹)
def uWord := W K (w++w)*(C K 0*C K 5*C K 1)*(W K (w++w))⁻¹
def squareWord := W K v*((W K [2,4]*C K 3*(W K [2,4])⁻¹)*
    (W K [3]*(C K 2*C K 4)*(W K [3])⁻¹))*(W K v)⁻¹

theorem yWord_eq : yWord K =
    yParameter K 0 1*yParameter K 1 1*yParameter K 2 1*yParameter K 3 1 := by
  have h0 := word_simple_one K [] 2 (yRoot 0) (by funext t; fin_cases t <;> decide)
  have h1 := word_simple_one K [] 4 (yRoot 1) (by funext t; fin_cases t <;> decide)
  have h2 := word_simple_one K [] 3 (yRoot 2) (by funext t; fin_cases t <;> decide)
  have h3 := word_simple_one K [2,4] 3 (yRoot 3) (by funext t; fin_cases t <;> decide)
  simp only [canonicalWord, one_mul, inv_one, mul_one] at h0 h1 h2
  exact congrArg₂ (fun a b => a*b)
    (congrArg₂ (fun a b => a*b) (congrArg₂ (fun a b => a*b) h0 h1) h2) h3

theorem uWord_eq : uWord K = uParameter K 0 1*uParameter K 1 1*uParameter K 2 1 := by
  have h0 := word_simple_one K (w++w) 0 (uRoot 0) (u_transport 0)
  have h1 := word_simple_one K (w++w) 5 (uRoot 1) (u_transport 1)
  have h2 := word_simple_one K (w++w) 1 (uRoot 2) (u_transport 2)
  calc
    _ = (W K (w++w)*C K 0*(W K (w++w))⁻¹)*
        (W K (w++w)*C K 5*(W K (w++w))⁻¹)*
        (W K (w++w)*C K 1*(W K (w++w))⁻¹) := by dsimp only [uWord]; group
    _ = _ := by rw [h0,h1,h2]; rfl

theorem squareWord_eq : squareWord K =
    bracketParameter K 0 1*bracketParameter K 1 1*bracketParameter K 2 1 := by
  have h2 := word_simple_one K (v++[2,4]) 3 (bracketRoot 2)
    (by funext t; fin_cases t <;> decide +kernel)
  have h0 := word_simple_one K (v++[3]) 2 (bracketRoot 0)
    (by funext t; fin_cases t <;> decide +kernel)
  have h1 := word_simple_one K (v++[3]) 4 (bracketRoot 1)
    (by funext t; fin_cases t <;> decide +kernel)
  rw [word_append K] at h2 h0 h1
  calc
    _ = ((W K v*W K [2,4])*C K 3*(W K v*W K [2,4])⁻¹)*
        ((W K v*W K [3])*C K 2*(W K v*W K [3])⁻¹)*
        ((W K v*W K [3])*C K 4*(W K v*W K [3])⁻¹) := by dsimp only [squareWord]; group
    _ = bracketParameter K 2 1*bracketParameter K 0 1*bracketParameter K 1 1 := by
      rw [h2,h0,h1]
      rfl
    _ = _ := by
      calc
        _ = bracketParameter K 2 1*(bracketParameter K 0 1*bracketParameter K 1 1) := mul_assoc _ _ _
        _ = (bracketParameter K 0 1*bracketParameter K 1 1)*bracketParameter K 2 1 :=
          ((bracket_commute K 2 0 1 1).mul_right (bracket_commute K 2 1 1 1)).eq

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareRootWordValues
