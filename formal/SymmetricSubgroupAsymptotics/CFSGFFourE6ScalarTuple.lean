import SymmetricSubgroupAsymptotics.CFSGFFourRelativeScalarIndex
import SymmetricSubgroupAsymptotics.CFSGRectangularMatrixPowerHom

/-! The literal four-to-six folded scalar embedding intertwines the two
integer Cartan exponent maps, in an arbitrary commutative group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6ScalarTuple
open CFSGFFourRelativeScalarIndex CFSGIntegerMatrixPowerHom
open CFSGRectangularMatrixPowerHom
variable {G : Type*} [CommGroup G]

def scalarTupleHom : (Fin 4→G)→*(Fin 6→G) where
  toFun x := ![x 0,x 3,x 1,x 2,x 1,x 0]
  map_one' := by funext i; fin_cases i <;> rfl
  map_mul' _ _ := by funext i; fin_cases i <;> rfl

def foldedCoordinate : Fin 6→Fin 4 := ![0,3,1,2,1,0]

def embedding : Matrix (Fin 6) (Fin 4) ℤ := coordinateEmbedding foldedCoordinate

theorem cartan_embedding : CartanMatrix.E₆*embedding=embedding*relativeCartan := by decide

theorem embedding_value (x : Fin 4→G) : matrixPowerHom embedding x=scalarTupleHom x := by
  funext i
  change matrixPowerHom (coordinateEmbedding foldedCoordinate) x i=scalarTupleHom x i
  rw [matrixPowerHom_coordinateEmbedding]
  fin_cases i <;> rfl

theorem powerHom_scalarTuple (x : Fin 4→G) :
    powerHom CartanMatrix.E₆ (scalarTupleHom x)=scalarTupleHom (powerHom relativeCartan x) := by
  change matrixPowerHom CartanMatrix.E₆ (scalarTupleHom x)=scalarTupleHom (matrixPowerHom relativeCartan x)
  calc
    _=matrixPowerHom CartanMatrix.E₆ (matrixPowerHom embedding x) :=
      congrArg (matrixPowerHom CartanMatrix.E₆) (embedding_value x).symm
    _=matrixPowerHom (CartanMatrix.E₆*embedding) x := (matrixPowerHom_mul _ _ x).symm
    _=matrixPowerHom (embedding*relativeCartan) x := congrArg (fun M=>matrixPowerHom M x) cartan_embedding
    _=matrixPowerHom embedding (matrixPowerHom relativeCartan x) := matrixPowerHom_mul _ _ x
    _=_ := embedding_value _

end SymmetricSubgroupAsymptotics.CFSGFFourE6ScalarTuple
