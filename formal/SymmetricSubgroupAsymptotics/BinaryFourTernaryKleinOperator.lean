import SymmetricSubgroupAsymptotics.BinaryFourTernaryAlternatingOperator

/-! A shared two-generator polynomial certificate for four ternary fibres.
The constants retain two two-point cycles. On augmentation, four actual
transports give a companion operator with a local ternary rotation. The
literal recurrence gives a uniform bound, including correlated submodules. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics
namespace BinaryFourTernaryKleinOperator

open BinaryFourTernaryCycleOperator

def columnMask : Fin 12 → ℕ :=
  ![2, 1361, 8, 1349, 32, 1301, 128, 1109, 512, 341, 2048, 1364]

def operator : Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  (binaryMatrixOfColumnMasks 12 columnMask).mulVecLin

def vectorMask : Fin 2 → Fin 10 → ℕ :=
  ![![1, 2, 1361, 2722, 16, 32, 1301, 2602, 256, 512],
    ![4, 8, 1349, 2698, 64, 128, 1109, 2218, 1024, 2048]]

def vectors (j : Fin 2) (m : Fin 10) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (vectorMask j m)

def selected : Fin 12 → Fin 2 × Fin 10 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (0, 6), (0, 7), (0, 8), (0, 9), (1, 0), (1, 1)]

def coefficientMask : Fin 12 → ℕ :=
  ![1, 2, 1024, 2048, 16, 32, 1092, 2184, 256, 512, 1361, 2722]

def coefficient (i : Fin 12) : Fin 12 → ZMod 2 :=
  binaryVectorOfMask 12 (coefficientMask i)

def polynomialWitness : LiteralPolynomialSpanWitness operator 2 9 where
  vectors := vectors
  step j m := by
    funext x
    revert j m x
    decide +kernel
  selected := selected
  coefficient := coefficient
  point_eq := by decide +kernel

variable {G : Type} [Group G]

def actualOperator (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t a : G) (q : Fin 4 → G) :
    Module.End (ZMod 2) (Fin 12 → ZMod 2) :=
  BinaryFourTernaryAlternatingOperator.constantsOperator singleBlock rho t a q * rho a +
    (∑ i : Fin 3, rho (q i.succ) * fibreOperator singleBlock rho t a *
      rho (q i.castSucc)⁻¹) +
    rho (localRotation singleBlock t a) * fibreOperator singleBlock rho t a * rho (q 3)⁻¹

def algebraElement (singleBlock : Bool) (t a : G) (q : Fin 4 → G) : (ZMod 2)[G] :=
  BinaryFourTernaryAlternatingOperator.constantsScalar singleBlock t a q *
      MonoidAlgebra.single a 1 +
    (∑ i : Fin 3, MonoidAlgebra.single (q i.succ) 1 * fibreScalar singleBlock t a *
      MonoidAlgebra.single (q i.castSucc)⁻¹ 1) +
    MonoidAlgebra.single (localRotation singleBlock t a) 1 * fibreScalar singleBlock t a *
      MonoidAlgebra.single (q 3)⁻¹ 1

theorem actualOperator_eq (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t a : G) (q : Fin 4 → G) :
    actualOperator singleBlock rho t a q =
      rho.asAlgebraHom (algebraElement singleBlock t a q) := by
  simp only [actualOperator, algebraElement, map_add, map_sum, map_mul,
    Representation.asAlgebraHom_single, one_smul, ← fibreOperator_eq,
    ← BinaryFourTernaryAlternatingOperator.constantsOperator_eq]

theorem uniform_of_basis (singleBlock : Bool)
    (rho : Representation (ZMod 2) G (Fin 12 → ZMod 2)) (t a : G) (q : Fin 4 → G)
    (e : Equiv.Perm (Fin 12))
    (h : ∀ i x : Fin 12,
      actualOperator singleBlock rho t a q
        (fun y ↦ (Pi.single i 1 : Fin 12 → ZMod 2) (e.symm y)) x =
          operator (Pi.single i 1) (e.symm x)) :
    UniformSubrepresentationGeneratorBound rho 2 :=
  polynomialWitness.uniform_of_reindexed_basis rho (algebraElement singleBlock t a q)
    (actualOperator singleBlock rho t a q) (actualOperator_eq singleBlock rho t a q) e h

end BinaryFourTernaryKleinOperator
end SymmetricSubgroupAsymptotics

end
