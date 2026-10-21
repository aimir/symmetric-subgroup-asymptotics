import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Ring

/-! Sparse binary D identities. An A1 rotation on two hyperbolic pairs
has order three. A root on two disjoint pairs has order two, so powers
separate their product. All matrices preserve the original D pairing;
no individual long-root transvection from type C is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryRotationArrays
open Matrix CFSGOrthogonalDSerreMatrices
variable {K : Type*} [CommRing K] [CharP K 2] {r : ℕ}

def shortArray (a b : Fin r) : Mat K r :=
  1 + Matrix.single (Sum.inl a) (Sum.inl b) 1 +
    Matrix.single (Sum.inr b) (Sum.inr a) 1

def rotationArray (a b : Fin r) : Mat K r :=
  shortArray a b * shortArray b a

def pairArray (a b c d : Fin r) : Mat K r :=
  rotationArray a b * shortArray c d

theorem short_square (a b : Fin r) (hab : a ≠ b) :
    shortArray (K := K) a b ^ 2 = 1 := by
  simp [shortArray, pow_two, add_mul, mul_add, hab, Ne.symm hab] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.one_apply]; ring_nf <;> try simp)

theorem rotation_cube (a b : Fin r) (hab : a ≠ b) :
    rotationArray (K := K) a b ^ 3 = 1 := by
  simp [rotationArray, shortArray, pow_succ, add_mul, mul_add, hab, Ne.symm hab] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.one_apply]; ring_nf <;> try simp)

theorem rotation_commutes_disjoint_short (a b c d : Fin r)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Commute (rotationArray (K := K) a b) (shortArray c d) := by
  change rotationArray a b * shortArray c d = shortArray c d * rotationArray (K := K) a b
  simp [rotationArray, shortArray, add_mul, mul_add,
    hac, had, hbc, hbd, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.one_apply]; ring_nf <;> try simp)

theorem pair_cube (a b c d : Fin r) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    pairArray (K := K) a b c d ^ 3 = shortArray c d := by
  rw [pairArray, (rotation_commutes_disjoint_short a b c d hac had hbc hbd).mul_pow,
    rotation_cube a b hab, one_mul]
  calc
    shortArray (K := K) c d ^ 3 = shortArray c d ^ 2 * shortArray c d := pow_succ _ 2
    _ = shortArray c d := by rw [short_square c d hcd, one_mul]

theorem pair_four (a b c d : Fin r) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    pairArray (K := K) a b c d ^ 4 = rotationArray a b := by
  rw [pairArray, (rotation_commutes_disjoint_short a b c d hac had hbc hbd).mul_pow]
  have hs : shortArray (K := K) c d ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, short_square c d hcd, one_pow]
  rw [hs, mul_one, show 4 = 3 + 1 from rfl, pow_succ, rotation_cube a b hab, one_mul]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryRotationArrays
