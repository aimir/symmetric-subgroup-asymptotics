import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-! A common cyclic algebra operator on three four-point blocks.
For a local Klein involution k, a ternary rotation r, and a block mover c,
put N=1+r+r² and T=c*(N*k*N+1+r²). The four literal realizations below
include twisted block movers. Twelve iterates of delta5 span in each case.

The polynomial PID theorem then makes every invariant subspace cyclic.
Only twelve-vector recurrences and their inverse matrices are certified;
no list of group elements or invariant subspaces enters the proof. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryTwistedAlternatingTriplePolynomial

def involution : Equiv.Perm (Fin 12) where
  toFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  invFun x := (#[0, 1, 11, 3, 4, 8, 6, 7, 5, 9, 10, 2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rotation (j : Fin 4) : Equiv.Perm (Fin 12) where
  toFun x := ((#[
    #[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2],
    #[0, 7, 5, 6, 4, 11, 9, 10, 8, 3, 1, 2],
    #[0, 1, 5, 9, 4, 11, 3, 7, 8, 6, 10, 2],
    #[0, 1, 5, 9, 4, 11, 3, 7, 8, 6, 10, 2]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  invFun x := ((#[
    #[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5],
    #[0, 10, 11, 9, 4, 2, 3, 1, 8, 6, 7, 5],
    #[0, 1, 11, 6, 4, 2, 9, 7, 8, 3, 10, 5],
    #[0, 1, 11, 6, 4, 2, 9, 7, 8, 3, 10, 5]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

def mover (j : Fin 4) : Equiv.Perm (Fin 12) where
  toFun x := ((#[
    #[2, 9, 10, 11, 0, 1, 5, 3, 4, 8, 6, 7],
    #[2, 0, 1, 11, 6, 7, 5, 3, 4, 8, 9, 10],
    #[4, 5, 9, 7, 8, 3, 10, 11, 0, 1, 2, 6],
    #[4, 2, 6, 10, 5, 9, 1, 11, 0, 7, 8, 3]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  invFun x := ((#[
    #[4, 5, 0, 7, 8, 6, 10, 11, 9, 1, 2, 3],
    #[1, 2, 0, 7, 8, 6, 4, 5, 9, 10, 11, 3],
    #[8, 9, 10, 5, 0, 1, 11, 3, 4, 2, 6, 7],
    #[8, 6, 1, 11, 0, 4, 2, 9, 10, 5, 3, 7]
    ] : Array (Array (Fin 12)))[j.val]!)[x.val]!
  left_inv := by revert j; decide +kernel
  right_inv := by revert j; decide +kernel

def representation :=
  permutationFunctionRepresentation (ZMod 2) (Equiv.Perm (Fin 12)) (Fin 12)

def averagingOperator (j : Fin 4) : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  1 + representation (rotation j) + representation ((rotation j) ^ 2)

def operator (j : Fin 4) : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  representation (mover j) *
    (averagingOperator j * representation involution * averagingOperator j + 1 +
      representation ((rotation j) ^ 2))

def vectorMask (j : Fin 4) (m : Fin 12) : ℕ :=
  ((#[
    #[32, 1042, 521, 2084, 16, 1, 4, 1168, 577, 2308, 128, 64],
    #[32, 146, 584, 2336, 128, 512, 2048, 1168, 577, 2308, 1024, 1],
    #[32, 521, 1042, 292, 512, 1024, 4, 577, 1168, 2308, 64, 128],
    #[32, 577, 1042, 292, 64, 1024, 256, 584, 1154, 2308, 8, 128]
    ] : Array (Array ℕ))[j.val]!)[m.val]!

def vectors (j : Fin 4) (_ : Fin 1) (m : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask j m)

def coefficientMask (j : Fin 4) (i : Fin 12) : ℕ :=
  ((#[
    #[32, 1154, 64, 2308, 16, 1, 2048, 1024, 521, 2336, 1168, 73],
    #[2048, 1154, 521, 2308, 1168, 1, 2336, 16, 73, 32, 1024, 64],
    #[1168, 2308, 64, 1154, 2336, 1, 1024, 2048, 73, 16, 32, 521],
    #[1154, 2336, 73, 1024, 2308, 1, 16, 2048, 64, 1168, 32, 521]
    ] : Array (Array ℕ))[j.val]!)[i.val]!

def coefficient (j : Fin 4) (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask j i)

private theorem step_checked : ∀ (j : Fin 4) (m : Fin 11) (x : Fin 12),
    vectors j 0 m.succ x = operator j (vectors j 0 m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ (j : Fin 4) (i x : Fin 12),
    (∑ m, coefficient j i m * vectors j 0 m x) =
      (Pi.single i 1 : Fin 12 → ZMod 2) x := by
  decide +kernel

def polynomialWitness (j : Fin 4) : LiteralPolynomialSpanWitness (operator j) 1 11 where
  vectors := vectors j
  step _ m := by
    funext x
    exact step_checked j m x
  selected m := (0, m)
  coefficient := coefficient j
  point_eq := point_checked j

def averagingElement {G : Type} [Group G] (r : G) : (ZMod 2)[G] :=
  1 + MonoidAlgebra.single r 1 + MonoidAlgebra.single (r ^ 2) 1

def algebraElement {G : Type} [Group G] (k r c : G) : (ZMod 2)[G] :=
  MonoidAlgebra.single c 1 *
    (averagingElement r * MonoidAlgebra.single k 1 * averagingElement r + 1 +
      MonoidAlgebra.single (r ^ 2) 1)

/-- Any acting group realizing one of these operator triples has a
uniform cyclic bound on the twelve-dimensional binary module. -/
theorem uniform {G : Type} [Group G] (j : Fin 4)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (k r c : G)
    (hk : rho k = representation involution)
    (hr : rho r = representation (rotation j))
    (hc : rho c = representation (mover j)) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply (polynomialWitness j).uniform rho (algebraElement k r c)
  simp only [operator, averagingOperator, algebraElement, averagingElement,
    map_mul, map_add, map_one, Representation.asAlgebraHom_single,
    one_smul, map_pow, hk, hr, hc]

/-- Literal permutation equalities bind the common operator proof directly
to the natural action of an actual subgroup. -/
theorem uniform_subgroup (j : Fin 4) (H : Subgroup (Equiv.Perm (Fin 12)))
    (k r c : H)
    (hk : (k : Equiv.Perm (Fin 12)) = involution)
    (hr : (r : Equiv.Perm (Fin 12)) = rotation j)
    (hc : (c : Equiv.Perm (Fin 12)) = mover j) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) H (Fin 12)) 1 := by
  have action_eq (g : H) (p : Equiv.Perm (Fin 12))
      (h : (g : Equiv.Perm (Fin 12)) = p) :
      permutationFunctionRepresentation (ZMod 2) H (Fin 12) g = representation p := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((g : Equiv.Perm (Fin 12))⁻¹ x) = v (p⁻¹ x)
    rw [h]
  exact uniform j _ k r c (action_eq k _ hk) (action_eq r _ hr) (action_eq c _ hc)

end BinaryTwistedAlternatingTriplePolynomial
end SymmetricSubgroupAsymptotics

end
