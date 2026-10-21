import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryRotationArrays

/-! Two sparse recovery identities for the binary D pair. The A1
rotation moves one star root to the adjacent star root. Ordinary star
commutators then recover all same-side chain roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped CharTwo
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryRotationArrays
open Matrix CFSGOrthogonalDSerreMatrices
variable {K : Type*} [CommRing K] [CharP K 2] {r : ℕ}

theorem rotation_star (a b c : Fin r) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    rotationArray (K := K) a b ^ 2 * shortArray c a * rotationArray a b = shortArray c b := by
  simp [rotationArray, shortArray, pow_two, add_mul, mul_add,
    hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.one_apply]; ring_nf <;> try simp)

theorem star_commutator (a b c : Fin r) (hab : a ≠ b)
    (hbc : b ≠ c) (hac : a ≠ c) :
    shortArray (K := K) a b * shortArray b c * shortArray a b * shortArray b c =
      shortArray a c := by
  simp [shortArray, add_mul, mul_add,
    hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc] <;>
    (ext i j; simp only [Matrix.add_apply, Matrix.one_apply]; ring_nf <;> try simp)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryRotationArrays
