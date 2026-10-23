import SymmetricSubgroupAsymptotics.CFSGFFourE6FoldedWeights
import SymmetricSubgroupAsymptotics.CFSGFFourGradedCartanAction
import SymmetricSubgroupAsymptotics.CFSGFFourFullRootAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree

/-! The actual integral F4 Cartans are the four displayed lattice-weight
diagonals. A kernel element of the SAME original-image action commutes
with these Cartans, by evaluating its action on the actual tensor-lattice
H generators. No faithfulness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6CartanDiagonals
open CFSGFFourSerreMatrices CFSGFFourE6FoldedWeights CFSGFFourGradedCartanAction
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoRootPairing CFSGIntegerMatrixPairing CFSGNormTwoGeckLatticeDegree
open CFSGSerreQuadraticMatrix

local instance cartanRootDecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _

abbrev rootWeight := latticeWeight CartanMatrix.E₆ CartanMatrix.E₆_transpose E6_positive_definite E6Base

def cartanFunctional (i : Fin 4) : (Fin 6 → ℤ) →+ ℤ :=
  ((integerPairing CartanMatrix.E₆).flip (orbitCartan i)).toAddMonoidHom

private theorem integral_e6_cartan_diagonal (j : Fin 6) :
    e6HZ j = Matrix.diagonal (fun a : Index=>
      integerPairing CartanMatrix.E₆ (rootWeight a) (Pi.single j (1 : ℤ))) := by
  have hp (k : Roots CartanMatrix.E₆) :
      E6Pairing.pairingIn ℤ k (E6Index j) =
        integerPairing CartanMatrix.E₆ k.val (Pi.single j (1 : ℤ)) := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℚ))
    have hc := E6Pairing.algebraMap_pairingIn ℤ k (E6Index j)
    change (E6Pairing.pairingIn ℤ k (E6Index j) : ℚ) = E6Pairing.pairing k (E6Index j) at hc
    exact hc.trans (pairing_cast CartanMatrix.E₆ CartanMatrix.E₆_transpose
      E6_positive_definite k (E6Index j))
  ext (a|a) (b|b) <;>
    simp [e6HZ,CFSGGeckIntegralMatrices.H,rootWeight,latticeWeight,Matrix.diagonal_apply,hp]

theorem integral_folded_cartan_diagonal (i : Fin 4) :
    integerH i = Matrix.diagonal (fun a : Index=>cartanFunctional i (rootWeight a)) := by
  fin_cases i
  · change e6HZ 0 + e6HZ 5 = Matrix.diagonal (fun a : Index=>
      integerPairing CartanMatrix.E₆ (rootWeight a)
        ((Pi.single 0 (1 : ℤ) : Fin 6 → ℤ) + Pi.single 5 1))
    rw [integral_e6_cartan_diagonal,integral_e6_cartan_diagonal,Matrix.diagonal_add]
    congr 1
    funext a
    exact (map_add (integerPairing CartanMatrix.E₆ (rootWeight a)) _ _).symm
  · change e6HZ 2 + e6HZ 4 = Matrix.diagonal (fun a : Index=>
      integerPairing CartanMatrix.E₆ (rootWeight a)
        ((Pi.single 2 (1 : ℤ) : Fin 6 → ℤ) + Pi.single 4 1))
    rw [integral_e6_cartan_diagonal,integral_e6_cartan_diagonal,Matrix.diagonal_add]
    congr 1
    funext a
    exact (map_add (integerPairing CartanMatrix.E₆ (rootWeight a)) _ _).symm
  · exact integral_e6_cartan_diagonal 3
  · exact integral_e6_cartan_diagonal 1

def fieldCartan (K : Type) [Field K] (i : Fin 4) : Matrix Index Index K :=
  (Int.castRingHom K).mapMatrix (integerH i)

theorem fieldCartan_eq_diagonal (K : Type) [Field K] (i : Fin 4) :
    fieldCartan K i = cartanDiagonal (K:=K) rootWeight (cartanFunctional i) := by
  rw [fieldCartan,integral_folded_cartan_diagonal]
  ext a b
  by_cases he : a=b <;> simp [cartanDiagonal,he]

theorem image_kernel_commutes_cartan (K : Type) [Field K]
    (g : canonicalElementaryGroup realizationData K)
    (hg : g∈(fullNaturalImageAction K).ker) (i : Fin 4) :
    Commute (g.val : Matrix Index Index K) (fieldCartan K i) := by
  let y : (baseChange realizationData K).range := (baseChange realizationData K).rangeRestrict
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.F₄ (.H i))
  have hy : y.val=fieldCartan K i := by
    change baseChange realizationData K
      (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.F₄ (.H i)) = _
    rw [baseChange_generator]
    rfl
  have he := DFunLike.congr_fun hg y
  have hh := congrArg Subtype.val he
  change (g.val : Matrix Index Index K) * y.val *
    (↑(g.val⁻¹) : Matrix Index Index K) = y.val at hh
  rw [hy] at hh
  have hm := congrArg (fun M : Matrix Index Index K=>M * (g.val : Matrix Index Index K)) hh
  simpa only [mul_assoc,Units.inv_mul,mul_one] using hm

end SymmetricSubgroupAsymptotics.CFSGFFourE6CartanDiagonals
