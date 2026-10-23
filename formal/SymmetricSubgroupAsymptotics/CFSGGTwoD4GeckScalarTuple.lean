import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckScalarTorus
import SymmetricSubgroupAsymptotics.CFSGRectangularMatrixPowerHom

/-! The literal two-to-four folded scalar embedding intertwines the two
integer Cartan exponent maps, in an arbitrary commutative group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckScalarTuple
open CFSGGTwoD4GeckScalarTorus CFSGIntegerMatrixPowerHom
open CFSGRectangularMatrixPowerHom
variable {G : Type*} [CommGroup G]

def scalarTupleHom : (Fin 2→G)→*(Fin 4→G) where
  toFun x := ![x 0,x 1,x 0,x 0]
  map_one' := by funext i; fin_cases i <;> rfl
  map_mul' _ _ := by funext i; fin_cases i <;> rfl

def foldedCoordinate : Fin 4→Fin 2 := ![0,1,0,0]

def embedding : Matrix (Fin 4) (Fin 2) ℤ := coordinateEmbedding foldedCoordinate

theorem cartan_embedding : (CartanMatrix.D 4)*embedding=embedding*relativeCartan := by decide

theorem embedding_value (x : Fin 2→G) : matrixPowerHom embedding x=scalarTupleHom x := by
  funext i
  change matrixPowerHom (coordinateEmbedding foldedCoordinate) x i=scalarTupleHom x i
  rw [matrixPowerHom_coordinateEmbedding]
  fin_cases i <;> rfl

theorem powerHom_scalarTuple (x : Fin 2→G) :
    powerHom (CartanMatrix.D 4) (scalarTupleHom x)=scalarTupleHom (powerHom relativeCartan x) := by
  change matrixPowerHom (CartanMatrix.D 4) (scalarTupleHom x)=scalarTupleHom (matrixPowerHom relativeCartan x)
  calc
    _=matrixPowerHom (CartanMatrix.D 4) (matrixPowerHom embedding x) :=
      congrArg (matrixPowerHom (CartanMatrix.D 4)) (embedding_value x).symm
    _=matrixPowerHom ((CartanMatrix.D 4)*embedding) x := (matrixPowerHom_mul _ _ x).symm
    _=matrixPowerHom (embedding*relativeCartan) x := congrArg (fun M=>matrixPowerHom M x) cartan_embedding
    _=matrixPowerHom embedding (matrixPowerHom relativeCartan x) := matrixPowerHom_mul _ _ x
    _=_ := embedding_value _

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckScalarTuple
