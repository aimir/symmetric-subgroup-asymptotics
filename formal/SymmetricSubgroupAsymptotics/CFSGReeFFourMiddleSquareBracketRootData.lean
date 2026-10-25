import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSignPilot

/-! A bounded E6 root-string pilot for the proposed middle-square
commutator relation. Only thirteen explicit lattice vectors, two literal
Weyl words and their pairings are checked. No field action or group-word
identity is asserted by these integer certificates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareBracketRootData
open CFSGReeFFourInversionSuffixSignPilot CFSGIntegerMatrixPairing
local notation "A" => CartanMatrix.E₆

def yVector : Fin 4 → Fin 6 → ℤ :=
  ![![0,0,1,0,0,0], ![0,0,0,0,1,0], ![0,0,0,1,0,0], ![0,0,1,1,1,0]]

def uVector : Fin 3 → Fin 6 → ℤ :=
  ![![1,1,1,2,1,0], ![0,1,1,2,1,1], ![1,1,2,2,2,1]]

def bracketVector : Fin 3 → Fin 6 → ℤ :=
  ![![1,1,2,2,1,0], ![0,1,1,2,2,1], ![1,1,2,3,2,1]]

private def squareVector : Fin 3 → Fin 6 → ℤ :=
  ![![0,0,1,1,0,0], ![0,0,0,1,1,0], ![0,0,1,1,1,0]]

private def outerNodes : Fin 3 → Fin 6 := ![0,5,1]
private def wRaw : List (Fin 6) := [0,5,1,2,4,3,2,4,3]
private def vRaw : List (Fin 6) := [2,4,3,2,4,3,0,5,1]

theorem norm_two :
    (∀ i : Fin 4, integerPairing A (yVector i) (yVector i) = 2) ∧
    (∀ i : Fin 3, integerPairing A (uVector i) (uVector i) = 2) ∧
    (∀ i : Fin 3, integerPairing A (bracketVector i) (bracketVector i) = 2) := by
  decide +kernel

private theorem u_transport_certificate : ∀ j : Fin 3, ∀ i : Fin 6,
    vectorWord (wRaw ++ wRaw) (Pi.single (outerNodes j) (1 : ℤ)) i = uVector j i := by
  decide +kernel

theorem u_transport (j : Fin 3) :
    vectorWord ([0,5,1,2,4,3,2,4,3] ++ [0,5,1,2,4,3,2,4,3])
      (Pi.single ((![0,5,1] : Fin 3 → Fin 6) j) (1 : ℤ)) = uVector j := by
  funext i
  exact u_transport_certificate j i

private theorem square_transport_certificate : ∀ j : Fin 3, ∀ i : Fin 6,
    vectorWord vRaw (squareVector j) i = bracketVector j i := by
  decide +kernel

theorem square_transport (j : Fin 3) :
    vectorWord [2,4,3,2,4,3,0,5,1]
      ((![![0,0,1,1,0,0], ![0,0,0,1,1,0], ![0,0,1,1,1,0]] :
        Fin 3 → Fin 6 → ℤ) j) = bracketVector j := by
  funext i
  exact square_transport_certificate j i

theorem pairing_table : ∀ i : Fin 4, ∀ j : Fin 3,
    integerPairing A (yVector i) (uVector j) =
      (![![-1,0,1], ![0,-1,1], ![1,1,-1], ![0,0,1]] : Fin 4 → Fin 3 → ℤ) i j := by
  decide +kernel

theorem sum_bracket : ∀ j : Fin 3, ∀ i : Fin 6,
    yVector j.castSucc i + uVector j i = bracketVector j i := by
  decide +kernel

theorem bracket_nonnegative_pairings :
    (∀ i : Fin 4, ∀ k : Fin 3, 0 ≤ integerPairing A (yVector i) (bracketVector k)) ∧
    (∀ j : Fin 3, ∀ k : Fin 3, 0 ≤ integerPairing A (uVector j) (bracketVector k)) ∧
    (∀ j k : Fin 3, 0 ≤ integerPairing A (bracketVector j) (bracketVector k)) := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareBracketRootData
