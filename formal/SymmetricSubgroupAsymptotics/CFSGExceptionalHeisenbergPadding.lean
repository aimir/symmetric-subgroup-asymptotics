import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergRootPilot

/-! The same selected twenty-one E6 roots occupy the first six simple
coordinates of E7 and E8. These finite integral certificates concern only
the ten displayed pairs and their one central sum. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergPadding
open CFSGExceptionalHeisenbergRootPilot
private def pad7 (v:Fin 6→ℤ) : Fin 7→ℤ := ![v 0,v 1,v 2,v 3,v 4,v 5,0]
private def pad8 (v:Fin 6→ℤ) : Fin 8→ℤ := ![v 0,v 1,v 2,v 3,v 4,v 5,0,0]

def E7 : RootConfig CartanMatrix.E₇ 10 where
  x i := pad7 (E6.x i)
  y i := pad7 (E6.y i)
  z := pad7 E6.z
  head := 1
  norm_x := by decide
  norm_y := by decide
  norm_z := by decide
  positive_x := by decide
  positive_y := by decide
  positive_z := by decide
  injective := by decide
  grade_x := by decide
  grade_y := by decide
  grade_z := by decide
  sum := by decide
  paired := by decide
  within_x := by decide
  within_y := by decide
  cross := by decide
  central_x := by decide
  central_y := by decide

def E8 : RootConfig CartanMatrix.E₈ 10 where
  x i := pad8 (E6.x i)
  y i := pad8 (E6.y i)
  z := pad8 E6.z
  head := 1
  norm_x := by decide
  norm_y := by decide
  norm_z := by decide
  positive_x := by decide
  positive_y := by decide
  positive_z := by decide
  injective := by decide
  grade_x := by decide
  grade_y := by decide
  grade_z := by decide
  sum := by decide
  paired := by decide
  within_x := by decide
  within_y := by decide
  cross := by decide
  central_x := by decide
  central_y := by decide

end SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergPadding
