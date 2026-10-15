import SymmetricSubgroupAsymptotics.BinaryTwistedAlternatingTriplePolynomial

/-! Two polynomial generators for three literal signed-pair operators.
The shared group-algebra formula is c*((1+r+r²)*k*(1+r+r²)+1+r²).
The displayed recurrence entries and inverse coefficients reconstruct all
twelve coordinate vectors. The polynomial/PID theorem then bounds every
actual invariant subspace, including correlated subspaces. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairTernaryAveragePolynomial

def columnMask (j : Fin 3) (i : Fin 12) : ℕ :=
  ((#[
    #[8, 128, 256, 32, 64, 1024, 512, 4, 2, 1, 2048, 16],
    #[1024, 440, 472, 2, 4, 496, 488, 2048, 1, 376, 248, 512],
    #[1024, 472, 440, 4, 2, 496, 488, 2048, 1, 376, 248, 512]
    ] : Array (Array ℕ))[j.val]!)[i.val]!

def operator (j : Fin 3) : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 (columnMask j)).mulVecLin

def vectorMask (j : Fin 3) (s : Fin 2) (m : Fin 8) : ℕ :=
  (((#[
    #[#[1, 8, 32, 1024, 2048, 16, 64, 512], #[2, 128, 4, 256, 2, 128, 4, 256]],
    #[#[1, 1024, 248, 2078, 614, 256, 1, 1024], #[2, 440, 2551, 3709, 1606, 8, 2, 440]],
    #[#[1, 1024, 248, 2078, 614, 256, 1, 1024], #[2, 472, 2543, 3709, 1574, 16, 2, 472]]
    ] : Array (Array (Array ℕ)))[j.val]!)[s.val]!)[m.val]!

def vectors (j : Fin 3) (s : Fin 2) (m : Fin 8) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask j s m)

def selected (j : Fin 3) (i : Fin 12) : Fin 2 × Fin 8 :=
  if j = 0 then
    (![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1] i,
      ![0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3] i)
  else
    (![0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1] i,
      ![0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5] i)

def coefficientMask (j : Fin 3) (i : Fin 12) : ℕ :=
  ((#[
    #[1, 256, 1024, 2, 32, 4, 64, 512, 2048, 128, 8, 16],
    #[1, 64, 539, 2048, 301, 1042, 164, 3487, 32, 1789, 2, 2942],
    #[1, 64, 539, 301, 2048, 164, 1042, 3487, 32, 1789, 2, 2942]
    ] : Array (Array ℕ))[j.val]!)[i.val]!

def coefficient (j : Fin 3) (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask j i)

private theorem step_checked : ∀ (j : Fin 3) (s : Fin 2) (m : Fin 7) (x : Fin 12),
    vectors j s m.succ x = operator j (vectors j s m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ (j : Fin 3) (i x : Fin 12),
    (∑ m, coefficient j i m * vectors j (selected j m).1 (selected j m).2 x) =
      (Pi.single i 1 : Fin 12 → ZMod 2) x := by
  decide +kernel

def polynomialWitness (j : Fin 3) : LiteralPolynomialSpanWitness (operator j) 2 7 where
  vectors := vectors j
  step s m := by
    funext x
    exact step_checked j s m x
  selected := selected j
  coefficient := coefficient j
  point_eq := point_checked j

def actualOperator {G : Type} [Group G]
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (k r c : G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  rho c * ((1 + rho r + rho (r ^ 2)) * rho k * (1 + rho r + rho (r ^ 2)) +
    1 + rho (r ^ 2))

theorem actualOperator_eq {G : Type} [Group G]
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (k r c : G) :
    actualOperator rho k r c =
      rho.asAlgebraHom (BinaryTwistedAlternatingTriplePolynomial.algebraElement k r c) := by
  simp only [actualOperator, BinaryTwistedAlternatingTriplePolynomial.algebraElement,
    BinaryTwistedAlternatingTriplePolynomial.averagingElement, map_mul, map_add,
    map_one, Representation.asAlgebraHom_single, one_smul]

/-- A basis check binds the literal matrix certificate to the actual
acting algebra; no vector or submodule census is assumed. -/
theorem uniform_of_basis {G : Type} [Group G] (j : Fin 3)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (k r c : G)
    (h : ∀ i x : Fin 12,
      actualOperator rho k r c (Pi.single i 1) x = operator j (Pi.single i 1) x) :
    UniformSubrepresentationGeneratorBound rho 2 := by
  have heq : actualOperator rho k r c = operator j := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (h i)
  apply (polynomialWitness j).uniform rho
    (BinaryTwistedAlternatingTriplePolynomial.algebraElement k r c)
  rw [← heq]
  exact actualOperator_eq rho k r c

end BinaryPairTernaryAveragePolynomial
end SymmetricSubgroupAsymptotics

end
