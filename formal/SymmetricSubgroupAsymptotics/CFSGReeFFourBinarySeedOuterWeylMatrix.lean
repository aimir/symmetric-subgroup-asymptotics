import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords

/-! ONE constant seed's26 sparse basis columns. No chart or centralizer
conclusion. Every finite equality is checked by the Lean kernel. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterWeylMatrix
open CFSGFFourNormPrimeFieldWords CFSGReeFFourMiddleDerivedFiveRootWords

def letters : List Letter := [(false,0),(true,0),(false,0),(false,3),(true,3),(false,3)]

def rows : Fin 26 → Finset (Fin 26) :=
  ![{0,1},
    {1},
    {3},
    {2},
    {4},
    {7},
    {12},
    {5},
    {11},
    {13},
    {14},
    {8},
    {6},
    {9},
    {10},
    {16},
    {15},
    {21},
    {20},
    {22},
    {18},
    {17},
    {19},
    {23},
    {25},
    {24} ]

def matrix : Matrix (Fin 26) (Fin 26) (ZMod 2) := fun i j =>
  if j∈rows i then 1 else 0

theorem matrix_entry : ∀i j : Fin 26,
    evaluate (ZMod 2) letters (fun k => if k=j then 1 else 0) i =
      matrix i j := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterWeylMatrix
