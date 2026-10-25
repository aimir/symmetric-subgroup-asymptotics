import SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldWords
import Init.Data.Vector.OfFn

/-! Materialized intermediate vectors for the checked constant-root action.
This file only proves evaluation semantics; it asserts no finite inequality. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldVectorEvaluation
open CFSGFFourNormPrimeFieldWords CFSGFFourNormCertificateSparseAction

variable (R : Type) [CommRing R]

def coordinates (v : Vector R 26) : Fin 26 → R := fun i => v[i.val]

def step (x : Letter) (v : Vector R 26) : Vector R 26 :=
  Vector.ofFn (sparseStep R x.1 x.2 1 (coordinates R v))

theorem coordinates_step (x : Letter) (v : Vector R 26) :
    coordinates R (step R x v) = sparseStep R x.1 x.2 1 (coordinates R v) := by
  funext i
  simp only [coordinates, step, Vector.getElem_ofFn]

def materialized (s : List Letter) (v : Vector R 26) : Vector R 26 :=
  s.foldr (step R) v

theorem coordinates_materialized (s : List Letter) (v : Vector R 26) :
    coordinates R (materialized R s v) = evaluate R s (coordinates R v) := by
  induction s with
  | nil => rfl
  | cons x s ih =>
    change coordinates R (step R x (materialized R s v)) =
      sparseStep R x.1 x.2 1 (evaluate R s (coordinates R v))
    rw [coordinates_step, ih]

end SymmetricSubgroupAsymptotics.CFSGFFourNormPrimeFieldVectorEvaluation
