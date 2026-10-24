import SymmetricSubgroupAsymptotics.CFSGIntegerRootCharacter
import SymmetricSubgroupAsymptotics.CFSGE6GeckProductTorusRootAction
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootDegrees

/-! The three actual middle A3 word characters, expressed through the
simple scalars of the same raw E6 product torus. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootCharacters
open CFSGIntegerRootCharacter CFSGIntegerMatrixPowerHom
open CFSGE6GeckProductTorusRootAction CFSGE6GeckMiddleRootDegrees
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoGeckWeylWordDegree
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

private theorem highest_vector :
    (![0,0,1,1,1,0] : Fin 6 → ℤ)=
      (Pi.single 2 1+Pi.single 3 1)+Pi.single 4 1 := by decide

private theorem first_vector :
    (![0,0,1,1,0,0] : Fin 6 → ℤ)=Pi.single 2 1+Pi.single 3 1 := by decide

private theorem second_vector :
    (![0,0,0,1,1,0] : Fin 6 → ℤ)=Pi.single 3 1+Pi.single 4 1 := by decide

theorem highest_character (K : Type) [Field K] (x : Fin 6 → Kˣ) :
    rootCharacter K x (wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3))=
      (powerHom A x 2*powerHom A x 3)*powerHom A x 4 := by
  change character A x (wordRoot A hs hp E6Base E6Index [2,4] (E6Index 3)).val=_
  rw [highest_root_degree,highest_vector,character_add,character_add,
    character_single A hs,character_single A hs,character_single A hs]

theorem paired_first_character (K : Type) [Field K] (x : Fin 6 → Kˣ) :
    rootCharacter K x (wordRoot A hs hp E6Base E6Index [3] (E6Index 2))=
      powerHom A x 2*powerHom A x 3 := by
  change character A x (wordRoot A hs hp E6Base E6Index [3] (E6Index 2)).val=_
  rw [paired_first_degree,first_vector,character_add,
    character_single A hs,character_single A hs]

theorem paired_second_character (K : Type) [Field K] (x : Fin 6 → Kˣ) :
    rootCharacter K x (wordRoot A hs hp E6Base E6Index [3] (E6Index 4))=
      powerHom A x 3*powerHom A x 4 := by
  change character A x (wordRoot A hs hp E6Base E6Index [3] (E6Index 4)).val=_
  rw [paired_second_degree,second_vector,character_add,
    character_single A hs,character_single A hs]

end SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleRootCharacters
