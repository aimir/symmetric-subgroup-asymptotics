import Mathlib.Algebra.Lie.Matrix
import Mathlib.Data.Matrix.Basis
import Lean.Elab.Tactic.Omega

/-!
# Natural matrices for the literal rank-r Serre A table

The pinned `CartanMatrix.A r` has r nodes. Its natural matrices consequently
act on `Fin (r+1)`. These are explicit matrices, with no group recognition
or simplicity premise. The selected rank-two Serre pilot is separate.
-/

set_option autoImplicit false
set_option Elab.async false

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices

variable (R : Type*) [CommRing R] (r : ℕ)

abbrev Mat := Matrix (Fin (r + 1)) (Fin (r + 1)) R

def positive (i : Fin r) : Mat R r := Matrix.single i.castSucc i.succ 1

def negative (i : Fin r) : Mat R r := (positive R r i).transpose

def cartan (i : Fin r) : Mat R r := ⁅positive R r i, negative R r i⁆

theorem positive_sq_zero (i : Fin r) : positive R r i ^ 2 = 0 := by
  have hne : i.succ ≠ i.castSucc := by
    intro h
    have hv := congrArg (fun j : Fin (r + 1) => j.val) h
    change i.val + 1 = i.val at hv
    omega
  simp [positive, pow_two, hne]

theorem negative_sq_zero (i : Fin r) : negative R r i ^ 2 = 0 := by
  rw [negative, pow_two, ← Matrix.transpose_mul, ← pow_two, positive_sq_zero]
  exact Matrix.transpose_zero

theorem map_positive {S : Type*} [CommRing S] (f : R →+* S) (i : Fin r) :
    f.mapMatrix (positive R r i) = positive S r i := by
  change (Matrix.single i.castSucc i.succ (1 : R)).map f = _
  simp only [Matrix.map_single, map_one, positive]

theorem map_negative {S : Type*} [CommRing S] (f : R →+* S) (i : Fin r) :
    f.mapMatrix (negative R r i) = negative S r i := by
  change (positive R r i).transpose.map f = (positive S r i).transpose
  rw [Matrix.transpose_map]
  exact congrArg Matrix.transpose (map_positive R r f i)

theorem map_cartan {S : Type*} [CommRing S] (f : R →+* S) (i : Fin r) :
    f.mapMatrix (cartan R r i) = cartan S r i := by
  simp only [cartan, Ring.lie_def, map_sub, map_mul, map_positive, map_negative]

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
