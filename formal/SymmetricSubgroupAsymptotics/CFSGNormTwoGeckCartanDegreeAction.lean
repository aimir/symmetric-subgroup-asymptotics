import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckLatticeDegree
import SymmetricSubgroupAsymptotics.CFSGGradedMatrixDiagonalLie

/-! The original rational Geck Cartan operator acts on every literal
lattice-degree matrix by its actual integer pairing. In particular this
applies to the SAME generated-Lie root words used for bracket recovery. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCartanDegreeAction
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckLatticeDegree
open CFSGGradedMatrixSupport CFSGGradedMatrixDiagonalLie
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

def degreeCharacter (i : b.support) : (n→ℤ)→+ℚ where
  toFun v := (integerPairing A v (i:Roots A).val:ℚ)
  map_zero' := by simp only [map_zero,LinearMap.zero_apply,Int.cast_zero]
  map_add' := by
    intro v w
    simp only [map_add,LinearMap.add_apply,Int.cast_add]

theorem cartan_eq_character_diagonal (i : b.support) :
    RootPairing.GeckConstruction.h i=
      Matrix.diagonal (fun j=>degreeCharacter A hs hp b i (latticeWeight A hs hp b j)) := by
  rw [RootPairing.GeckConstruction.h_eq_diagonal]
  congr 1
  funext j
  cases j with
  | inl j=>simp only [Sum.elim_inl,latticeWeight,map_zero,Pi.zero_apply]
  | inr j=>
    change algebraMap ℤ ℚ ((rootPairing A hs hp).pairingIn ℤ j i)=
      (integerPairing A j.val (i:Roots A).val:ℚ)
    rw [RootPairing.algebraMap_pairingIn]
    exact pairing_cast A hs hp j i

theorem cartan_lie_of_lattice_degree (i : b.support) (d : n→ℤ)
    (M : Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)
    (hM : Supported (latticeWeight A hs hp b) (fun v=>v+d) M) :
    ⁅RootPairing.GeckConstruction.h i,M⁆=(integerPairing A d (i:Roots A).val:ℚ) • M := by
  rw [cartan_eq_character_diagonal A hs hp b i]
  exact diagonal_lie_of_supported (latticeWeight A hs hp b)
    (degreeCharacter A hs hp b i) d M hM

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCartanDegreeAction
