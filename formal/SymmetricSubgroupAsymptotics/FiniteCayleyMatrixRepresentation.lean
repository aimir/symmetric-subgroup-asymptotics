import SymmetricSubgroupAsymptotics.FiniteCayleyMaps
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RepresentationTheory.Basic

/-!
# Matrix representations checked on a finite Cayley row

The selected finite-frame exporters store one invertible matrix for every
original top generator.  The Cayley certificate already stores a positive
generator word for every row.  Consequently the representation law can be
checked only on the right-generator transitions, instead of emitting a
quadratic multiplication table.

This file is independent of the degree-eight catalogue.  Generated rows
provide literal forward and inverse matrices, the two inverse equations,
and the finitely many Cayley transition equations.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {k G iota Code : Type*} [Field k] [Group G]
  {generators : iota → G} {E : GeneratorEncoding generators Code}
  {n d : ℕ}

/-- Package an explicitly checked inverse matrix as a matrix unit. -/
def checkedMatrixUnit
    (forward inverse : Matrix (Fin d) (Fin d) k)
    (forward_inverse : forward * inverse = 1)
    (inverse_forward : inverse * forward = 1) :
    Units (Matrix (Fin d) (Fin d) k) where
  val := forward
  inv := inverse
  val_inv := forward_inverse
  inv_val := inverse_forward

/-- A matrix-valued group homomorphism acts on column vectors by
left multiplication. -/
def matrixUnitRepresentation
    (phi : G →* Units (Matrix (Fin d) (Fin d) k)) :
    Representation k G (Fin d → k) where
  toFun g := ((phi g : Units (Matrix (Fin d) (Fin d) k)) :
    Matrix (Fin d) (Fin d) k).mulVecLin
  map_one' := by
    apply LinearMap.ext
    intro v
    change ((↑(phi 1) : Matrix (Fin d) (Fin d) k).mulVec v) = v
    rw [map_one]
    exact Matrix.one_mulVec v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    change ((↑(phi (g * h)) : Matrix (Fin d) (Fin d) k).mulVec v) =
      (↑(phi g) : Matrix (Fin d) (Fin d) k).mulVec
        ((↑(phi h) : Matrix (Fin d) (Fin d) k).mulVec v)
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

namespace EncodedCayleyCertificate

variable (C : EncodedCayleyCertificate E n)

/-- The matrix unit obtained by evaluating the certified positive word of a
Cayley row on the displayed generator matrices. -/
def matrixWordValue
    (images : iota → Units (Matrix (Fin d) (Fin d) k))
    (i : Fin n) : Units (Matrix (Fin d) (Fin d) k) :=
  ((C.words i).map images).prod

/-- Transition equations on the finite Cayley graph produce the complete
matrix homomorphism.  Generated files prove `hstep` by finite reduction on
the literal matrices. -/
def checkedMatrixHom
    (images : iota → Units (Matrix (Fin d) (Fin d) k))
    (hstep : ∀ i j,
      C.matrixWordValue images (C.next i j) =
        C.matrixWordValue images i * images j)
    (hinj : Function.Injective C.rows)
    (prev : Fin n → iota → Fin n)
    (hprev : ∀ i j, C.next (prev i j) j = i) :
    letI := C.rowGroup hinj prev hprev
    FiniteGroupRow n →* Units (Matrix (Fin d) (Fin d) k) := by
  letI := C.rowGroup hinj prev hprev
  exact C.checkedHom (C.matrixWordValue images) images hstep hinj prev hprev
    (by simp only [matrixWordValue, C.words_identity, List.map_nil,
      List.prod_nil])

/-- The checked matrix homomorphism, regarded as a linear representation of
the executable row group. -/
def checkedMatrixRepresentation
    (images : iota → Units (Matrix (Fin d) (Fin d) k))
    (hstep : ∀ i j,
      C.matrixWordValue images (C.next i j) =
        C.matrixWordValue images i * images j)
    (hinj : Function.Injective C.rows)
    (prev : Fin n → iota → Fin n)
    (hprev : ∀ i j, C.next (prev i j) j = i) :
    letI := C.rowGroup hinj prev hprev
    Representation k (FiniteGroupRow n) (Fin d → k) := by
  letI := C.rowGroup hinj prev hprev
  exact matrixUnitRepresentation
    (C.checkedMatrixHom images hstep hinj prev hprev)

@[simp] theorem checkedMatrixRepresentation_apply
    (images : iota → Units (Matrix (Fin d) (Fin d) k))
    (hstep : ∀ i j,
      C.matrixWordValue images (C.next i j) =
        C.matrixWordValue images i * images j)
    (hinj : Function.Injective C.rows)
    (prev : Fin n → iota → Fin n)
    (hprev : ∀ i j, C.next (prev i j) j = i)
    (g : FiniteGroupRow n) (v : Fin d → k) :
    letI := C.rowGroup hinj prev hprev
    C.checkedMatrixRepresentation images hstep hinj prev hprev g v =
      ((C.matrixWordValue images g.index :
        Units (Matrix (Fin d) (Fin d) k)) :
          Matrix (Fin d) (Fin d) k).mulVec v := by
  letI := C.rowGroup hinj prev hprev
  rfl

end EncodedCayleyCertificate
end SymmetricSubgroupAsymptotics

end
