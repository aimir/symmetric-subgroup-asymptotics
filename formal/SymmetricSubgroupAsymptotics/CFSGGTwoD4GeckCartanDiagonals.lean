import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFoldedWeights
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckImageRealization
import SymmetricSubgroupAsymptotics.CFSGFFourGradedCartanAction
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree

/-! The TWO actual original G2 Cartan generators are the displayed D4
lattice-weight diagonals. A kernel element of the SAME cubic integral
image action commutes with both, by evaluating on original H tensors.
This lemma makes no representation-faithfulness assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckCartanDiagonals
open CFSGGTwoD4GeckGenerators CFSGGTwoD4GeckIntegralRealization
open CFSGGTwoD4GeckImageRealization CFSGGTwoD4GeckFoldedWeights
open CFSGTrialityD4NormTwo CFSGNormTwoRootPairing CFSGIntegerMatrixPairing
open CFSGNormTwoGeckLatticeDegree CFSGFFourGradedCartanAction
local notation "A" => CartanMatrix.D 4
local notation "hs" => CartanMatrix.D_transpose 4
local notation "hp" => D4_positive_definite

abbrev rootWeight := latticeWeight A hs hp Base

def cartanFunctional (i : Fin 2) : (Fin 4→ℤ)→+ℤ :=
  ((integerPairing A).flip (orbitCartan i)).toAddMonoidHom

private theorem integral_d4_cartan_diagonal (j : Fin 4) :
    CFSGGeckIntegralMatrices.H Base (Index j)=Matrix.diagonal (fun a : GeckIndex=>
      integerPairing A (rootWeight a) (Pi.single j (1:ℤ))) := by
  have hpair (k : Roots A) : Pairing.pairingIn ℤ k (Index j)=
      integerPairing A k.val (Pi.single j (1:ℤ)) := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
    have hc := Pairing.algebraMap_pairingIn ℤ k (Index j)
    change (Pairing.pairingIn ℤ k (Index j):ℚ)=Pairing.pairing k (Index j) at hc
    exact hc.trans (pairing_cast A hs hp k (Index j))
  ext (a|a) (b|b) <;>
    simp [CFSGGeckIntegralMatrices.H,rootWeight,latticeWeight,Matrix.diagonal_apply,hpair]

theorem integral_folded_cartan_diagonal (i : Fin 2) :
    integerH i=Matrix.diagonal (fun a : GeckIndex=>cartanFunctional i (rootWeight a)) := by
  fin_cases i
  · change CFSGGeckIntegralMatrices.H Base (Index 0)+CFSGGeckIntegralMatrices.H Base (Index 2)+
      CFSGGeckIntegralMatrices.H Base (Index 3)=Matrix.diagonal (fun a : GeckIndex=>
        integerPairing A (rootWeight a)
          ((Pi.single 0 (1:ℤ):Fin 4→ℤ)+Pi.single 2 1+Pi.single 3 1))
    rw [integral_d4_cartan_diagonal,integral_d4_cartan_diagonal,integral_d4_cartan_diagonal,
      Matrix.diagonal_add,Matrix.diagonal_add]
    congr 1
    funext a
    simp only [Pi.add_apply,map_add]
  · exact integral_d4_cartan_diagonal 1

def fieldCartan (K : Type) [Field K] (i : Fin 2) : Matrix GeckIndex GeckIndex K :=
  (Int.castRingHom K).mapMatrix (integerH i)

theorem fieldCartan_eq_diagonal (K : Type) [Field K] (i : Fin 2) :
    fieldCartan K i=cartanDiagonal (K:=K) rootWeight (cartanFunctional i) := by
  rw [fieldCartan,integral_folded_cartan_diagonal]
  ext a b
  by_cases he : a=b <;> simp [cartanDiagonal,he]

theorem image_kernel_commutes_cartan (K : Type) [Field K] (g : foldedGroup K)
    (hg : g∈(foldedImageAction K).ker) (i : Fin 2) :
    Commute (g.val : Matrix GeckIndex GeckIndex K) (fieldCartan K i) := by
  let y : Image K := (CFSGSerreCubicMatrix.baseChange realizationData K).rangeRestrict
    (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (.H i))
  have hy : y.val=fieldCartan K i := by
    change CFSGSerreCubicMatrix.baseChange realizationData K
      (1 ⊗ₜ[ℤ] CFSGSerreDiagram.latticeGenerator CartanMatrix.G₂ (.H i))=_
    rw [CFSGSerreCubicMatrix.baseChange_generator]
    rfl
  have he := DFunLike.congr_fun hg y
  have hh := congrArg Subtype.val he
  change (g.val : Matrix GeckIndex GeckIndex K)*y.val*(↑(g.val⁻¹):Matrix GeckIndex GeckIndex K)=y.val at hh
  rw [hy] at hh
  have hm := congrArg (fun M : Matrix GeckIndex GeckIndex K=>M*(g.val : Matrix GeckIndex GeckIndex K)) hh
  simpa only [mul_assoc,Units.inv_mul,mul_one] using hm

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckCartanDiagonals
