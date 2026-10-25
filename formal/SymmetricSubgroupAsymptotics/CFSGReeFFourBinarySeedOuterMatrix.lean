import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleDerivedFiveRootWords

/-! Selected two-root norm26 matrix pilot. The only finite computation
binds the literal outer root word on its26 basis columns. No other seed,
ordered-chart constraint, centralizer or group equality is asserted. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterMatrix
open CFSGFFourNormPrimeFieldWords CFSGReeFFourMiddleDerivedFiveRootWords

def outerRows : Fin 26 → Finset (Fin 26) :=
  ![{0,10},
    {1},
    {2},
    {2,3},
    {4},
    {5},
    {6},
    {5,7},
    {6,8},
    {9},
    {10},
    {6,11},
    {6,8,11,12},
    {9,13},
    {1,10,14},
    {15},
    {15,16},
    {17},
    {17,18},
    {19},
    {17,20},
    {17,18,20,21},
    {19,22},
    {23},
    {24},
    {24,25} ]

def outerMatrix : Matrix (Fin 26) (Fin 26) (ZMod 2) := fun i j =>
  if j∈outerRows i then 1 else 0

theorem outer_matrix_entry : ∀i j : Fin 26,
    evaluate (ZMod 2) outerLetters (fun k => if k=j then 1 else 0) i =
      outerMatrix i j := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGReeFFourBinarySeedOuterMatrix
