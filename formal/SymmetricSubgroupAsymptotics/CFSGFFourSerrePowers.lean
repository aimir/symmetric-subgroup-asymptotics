import SymmetricSubgroupAsymptotics.CFSGFFourRootNonzero
import SymmetricSubgroupAsymptotics.CFSGFiniteSlTwoSerre

/-! The final two actual F4 Serre relations follow from the proved sl2
triples in the finite-dimensional original E6 Geck representation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
local instance fFourPowersDecEq : DecidableEq
    (CFSGNormTwoRootPairing.Roots CartanMatrix.E₆) := Classical.decEq _

theorem positive_serre (i j : Fin 4) :
    (LieAlgebra.ad ℚ Mat (positive i)^(-CartanMatrix.F₄ i j).toNat) ⁅positive i,positive j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · have hf : ⁅negative i,positive j⁆=0 := by
      have hh : ⁅positive j,negative i⁆=0 := by rw [EF,if_neg (Ne.symm hij)]
      calc
        _= -⁅positive j,negative i⁆ := (lie_skew _ _).symm
        _=0 := by rw [hh,neg_zero]
    exact CFSGFiniteSlTwoSerre.serre_of_integer_weight (sl2Triple i) (positive j)
      (CartanMatrix.F₄ i j) (CartanMatrix.F₄_off_diag_nonpos i j hij) (HE i j) hf

theorem negative_serre (i j : Fin 4) :
    (LieAlgebra.ad ℚ Mat (negative i)^(-CartanMatrix.F₄ i j).toNat) ⁅negative i,negative j⁆=0 := by
  by_cases hij : i=j
  · subst j
    rw [lie_self,map_zero]
  · have hh : ⁅-(cartan i),negative j⁆=CartanMatrix.F₄ i j • negative j := by
      rw [neg_lie,HF,neg_neg]
    have he : ⁅positive i,negative j⁆=0 := by rw [EF,if_neg hij]
    exact CFSGFiniteSlTwoSerre.serre_of_integer_weight (sl2Triple i).symm (negative j)
      (CartanMatrix.F₄ i j) (CartanMatrix.F₄_off_diag_nonpos i j hij) hh he

end SymmetricSubgroupAsymptotics.CFSGFFourSerreMatrices
