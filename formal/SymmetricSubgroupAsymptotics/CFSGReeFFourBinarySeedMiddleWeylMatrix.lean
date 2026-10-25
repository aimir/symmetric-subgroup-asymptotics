import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords

/-! ONE constant seed's26 sparse basis columns. No chart or centralizer
conclusion. Every finite equality is checked by the Lean kernel. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleWeylMatrix
open CFSGFFourNormPrimeFieldWords CFSGReeFFourMiddleDerivedFiveRootWords

def letters : List Letter := [(false,1),(true,1),(false,1),(false,2),(true,2),(false,2),(false,1),(true,1),(false,1),(false,2),(true,2),(false,2)]

def rows : Fin 26 → Finset (Fin 26) :=
  ![{0},
    {1},
    {2},
    {6},
    {5},
    {4},
    {3},
    {10},
    {9},
    {8},
    {7},
    {11},
    {17},
    {15},
    {19},
    {13},
    {18},
    {12},
    {16},
    {14},
    {20},
    {24},
    {23},
    {22},
    {21},
    {25} ]

def matrix : Matrix (Fin 26) (Fin 26) (ZMod 2) := fun i j =>
  if j∈rows i then 1 else 0

theorem matrix_entry : ∀i j : Fin 26,
    evaluate (ZMod 2) letters (fun k => if k=j then 1 else 0) i =
      matrix i j := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedMiddleWeylMatrix
