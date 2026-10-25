import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareBracketRootData

/-! Selected integral root arrows inside the actual outer strict radical.
The first arrows come from y against its outer-Weyl conjugate; further
arrows reach all three roots of the middle-Weyl outer parameter. These
are root-pair certificates only: product coverage, exceptional fixedness
and cancellation in an entire double commutator are NOT assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOuterKernelBracketRootData
open CFSGReeFFourMiddleSquareBracketRootData CFSGReeFFourInversionSuffixSignPilot
open CFSGIntegerMatrixPairing
local notation "A" => CartanMatrix.E₆

def reflectedY : Fin 4 → Fin 6 → ℤ :=
  ![![1,0,1,0,0,0], ![0,0,0,0,1,1], ![0,1,0,1,0,0], ![1,1,1,1,1,1]]

def firstBracket : Fin 4 → Fin 6 → ℤ :=
  ![![0,1,1,1,0,0], ![0,1,0,1,1,0], ![1,0,1,1,0,0], ![0,0,0,1,1,1]]

def outerImage : Fin 3 → Fin 6 → ℤ :=
  ![![1,0,1,1,1,0], ![0,0,1,1,1,1], ![0,1,1,2,1,0]]

def bridge : Fin 6 → ℤ := ![0,1,1,1,1,0]

theorem root_properties :
    (∀ i : Fin 4, integerPairing A (reflectedY i) (reflectedY i) = 2 ∧
      ∀ t : Fin 6, 0 ≤ reflectedY i t) ∧
    (∀ i : Fin 4, integerPairing A (firstBracket i) (firstBracket i) = 2 ∧
      ∀ t : Fin 6, 0 ≤ firstBracket i t) ∧
    (∀ i : Fin 3, integerPairing A (outerImage i) (outerImage i) = 2 ∧
      ∀ t : Fin 6, 0 ≤ outerImage i t) ∧
    (integerPairing A bridge bridge = 2 ∧ ∀ t : Fin 6, 0 ≤ bridge t) := by
  decide +kernel

theorem outer_transport (i : Fin 4) :
    vectorWord [0,5,1] (yVector i) = reflectedY i := by
  funext t
  fin_cases i <;> fin_cases t <;> decide +kernel

theorem middle_transport (i : Fin 3) :
    vectorWord [2,4,3,2,4,3]
      (Pi.single ((![0,5,1] : Fin 3 → Fin 6) i) (1 : ℤ)) = outerImage i := by
  funext t
  fin_cases i <;> fin_cases t <;> decide +kernel

theorem cross_pairings : ∀ i j : Fin 4,
    integerPairing A (yVector i) (reflectedY j) =
      (![![1,0,-1,0], ![0,1,-1,0], ![-1,-1,1,-1], ![0,0,-1,-1]] :
        Fin 4 → Fin 4 → ℤ) i j := by
  decide +kernel

theorem first_arrows : ∀ i : Fin 4,
    integerPairing A (yVector ((![0,1,2,2] : Fin 4 → Fin 4) i))
      (reflectedY ((![2,2,0,1] : Fin 4 → Fin 4) i)) = -1 ∧
    ∀ t : Fin 6,
      yVector ((![0,1,2,2] : Fin 4 → Fin 4) i) t +
        reflectedY ((![2,2,0,1] : Fin 4 → Fin 4) i) t = firstBracket i t := by
  decide +kernel

theorem second_arrows :
    (integerPairing A (firstBracket 2) (yVector 1) = -1 ∧
      ∀ t : Fin 6, firstBracket 2 t+yVector 1 t = outerImage 0 t) ∧
    (integerPairing A (firstBracket 3) (yVector 0) = -1 ∧
      ∀ t : Fin 6, firstBracket 3 t+yVector 0 t = outerImage 1 t) ∧
    (integerPairing A (firstBracket 0) (yVector 1) = -1 ∧
      ∀ t : Fin 6, firstBracket 0 t+yVector 1 t = bridge t) := by
  decide +kernel

theorem third_arrow : integerPairing A bridge (yVector 2) = -1 ∧
    ∀ t : Fin 6, bridge t+yVector 2 t = outerImage 2 t := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourOuterKernelBracketRootData
