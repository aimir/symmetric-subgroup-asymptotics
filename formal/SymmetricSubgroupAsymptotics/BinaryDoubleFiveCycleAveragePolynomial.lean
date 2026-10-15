import SymmetricSubgroupAsymptotics.BinaryFiveCycleAveragePolynomial

/-! A shared two-generator polynomial bound for two five-cycle orbits.
The operator is E*b*E+1+a², with E=1+a+a²+a³+a⁴. For the three displayed
coordinate realizations, two six-term recurrences span all twelve points.
The same uniform polynomial/PID argument applies to every actual
subrepresentation of any group realizing these operators. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryDoubleFiveCycleAveragePolynomial

def columnMask (j : Fin 3) (i : Fin 12) : ℕ :=
  ((#[
    #[1041, 546, 1092, 648, 1296, 2592, 1089, 642, 1284, 2218, 341, 2568],
    #[682, 35, 2116, 137, 2320, 545, 3136, 131, 2308, 521, 3088, 1364],
    #[1364, 2082, 69, 2184, 273, 2592, 1089, 2178, 261, 2568, 1041, 682]
    ] : Array (Array ℕ))[j.val]!)[i.val]!

def operator (j : Fin 3) : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 (columnMask j)).mulVecLin

def vectorMask (j : Fin 3) (s : Fin 2) (m : Fin 6) : ℕ :=
  (((#[
    #[#[1, 1041, 84, 1301, 276, 1104], #[2, 546, 168, 2602, 2088, 672]],
    #[#[2, 35, 168, 555, 552, 161], #[4, 2116, 336, 3156, 1104, 2368]],
    #[#[2, 2082, 168, 2602, 552, 2208], #[4, 69, 336, 1109, 1104, 321]]
    ] : Array (Array (Array ℕ)))[j.val]!)[s.val]!)[m.val]!

def vectors (j : Fin 3) (s : Fin 2) (m : Fin 6) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask j s m)

def selected (i : Fin 12) : Fin 2 × Fin 6 :=
  (finProdFinEquiv : Fin 2 × Fin 6 ≃ Fin 12).symm i

def coefficientMask (j : Fin 3) (i : Fin 12) : ℕ :=
  ((#[
    #[1, 64, 61, 3904, 26, 1664, 35, 2240, 55, 1600, 25, 3520],
    #[25, 1, 64, 61, 3904, 26, 1664, 35, 2240, 55, 3520, 1600],
    #[1600, 1, 64, 61, 3904, 26, 1664, 35, 2240, 55, 3520, 25]
    ] : Array (Array ℕ))[j.val]!)[i.val]!

def coefficient (j : Fin 3) (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask j i)

private theorem step_checked : ∀ (j : Fin 3) (s : Fin 2) (m : Fin 5) (x : Fin 12),
    vectors j s m.succ x = operator j (vectors j s m.castSucc) x := by
  decide +kernel

private theorem point_checked : ∀ (j : Fin 3) (i x : Fin 12),
    (∑ m, coefficient j i m * vectors j (selected m).1 (selected m).2 x) =
      (Pi.single i 1 : Fin 12 → ZMod 2) x := by
  decide +kernel

def polynomialWitness (j : Fin 3) : LiteralPolynomialSpanWitness (operator j) 2 5 where
  vectors := vectors j
  step s m := by
    funext x
    exact step_checked j s m x
  selected := selected
  coefficient := coefficient j
  point_eq := point_checked j

/-- The original five-cycle-average operator is checked on a basis;
polynomial spanning bounds every actual invariant subspace by two. -/
theorem uniform_of_basis {G : Type} [Group G] (j : Fin 3)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (a b : G)
    (h : ∀ i x : Fin 12,
      BinaryFiveCycleAveragePolynomial.actualOperator rho a b 1 (Pi.single i 1) x =
        operator j (Pi.single i 1) x) :
    UniformSubrepresentationGeneratorBound rho 2 := by
  have heq : BinaryFiveCycleAveragePolynomial.actualOperator rho a b 1 = operator j := by
    apply (Pi.basisFun (ZMod 2) (Fin 12)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (h i)
  apply (polynomialWitness j).uniform rho
    (BinaryFiveCycleAveragePolynomial.algebraElement a b 1)
  rw [← heq]
  exact BinaryFiveCycleAveragePolynomial.actualOperator_eq rho a b 1

end BinaryDoubleFiveCycleAveragePolynomial
end SymmetricSubgroupAsymptotics

end
