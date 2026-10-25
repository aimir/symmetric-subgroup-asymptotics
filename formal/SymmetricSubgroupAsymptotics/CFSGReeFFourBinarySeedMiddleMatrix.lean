import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords

/-! ONE constant seed's26 sparse basis columns. No chart or centralizer
conclusion. Every finite equality is checked by the Lean kernel. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleMatrix
open CFSGFFourNormPrimeFieldWords CFSGReeFFourMiddleDerivedFiveRootWords

def letters : List Letter := [(false,1),(false,2),(false,1),(true,1),(false,1),(false,2),(false,1),(true,1),(false,1)]

def rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1,12,13},
    {2},
    {3},
    {3,4},
    {4,5},
    {3,4,5,6},
    {7},
    {7,8},
    {8,9},
    {7,8,9,10},
    {11},
    {12},
    {12,13},
    {14},
    {0,13,15},
    {14,16},
    {12,13,15,17},
    {16,18},
    {14,16,18,19},
    {20},
    {21},
    {21,22},
    {22,23},
    {21,22,23,24},
    {25} ]

def matrix : Matrix (Fin 26) (Fin 26) (ZMod 2) := fun i j =>
  if j∈rows i then 1 else 0

theorem matrix_entry : ∀i j : Fin 26,
    evaluate (ZMod 2) letters (fun k => if k=j then 1 else 0) i =
      matrix i j := by
  decide +kernel

theorem letters_eq_fourCycle : letters=fourCycleLetters := rfl

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleMatrix
