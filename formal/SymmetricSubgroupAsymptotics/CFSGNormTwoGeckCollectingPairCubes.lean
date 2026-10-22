import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
import SymmetricSubgroupAsymptotics.CFSGUnitConjugationNilpotence

/-! Actual commuting cubic-nilpotent pairs for adjacent positive-root
collecting. Every cube vanishes in the SAME Geck matrix algebra: the
bracket and sum are actual conjugates of the original simple root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCollectingPairCubes
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckParameterizedWeyl
open CFSGNormTwoGeckRationalWeylCollecting CFSGUnitConjugationNilpotence
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem cartan_symmetric (i j : Fin r) : cartan b s i j=cartan b s j i := by
  apply (Int.cast_injective : Function.Injective (Int.cast : ℤ→ℚ))
  change algebraMap ℤ ℚ (b.cartanMatrixIn ℤ (s j) (s i))=
    algebraMap ℤ ℚ (b.cartanMatrixIn ℤ (s i) (s j))
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply,
    RootPairing.Base.algebraMap_cartanMatrixIn_apply,pairing_cast,pairing_cast,
    integer_symmetric A hs (s j:Roots A).val (s i:Roots A).val]

theorem root_cube (i : Fin r) : (fieldRoot (realizationData A hs hp b s) ℚ false i)^3=0 := by
  rw [pow_succ,pow_two,fieldRoot_square,add_mul,fieldSecond_mul_root,add_zero]

theorem collecting_pair_commute (i j : Fin r) (hij : cartan b s i j= -1) :
    Commute (fieldRoot (realizationData A hs hp b s) ℚ false j)
      ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
        fieldRoot (realizationData A hs hp b s) ℚ false j⁆ := by
  have hji : cartan b s j i= -1 := (cartan_symmetric A hs hp b s j i).trans hij
  have hh := double_lie_of_cartan_neg_one A hs hp b s j i hji
  have he : ⁅fieldRoot (realizationData A hs hp b s) ℚ false j,
      ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
        fieldRoot (realizationData A hs hp b s) ℚ false j⁆⁆=0 := by
    calc
      _= -⁅fieldRoot (realizationData A hs hp b s) ℚ false j,
        ⁅fieldRoot (realizationData A hs hp b s) ℚ false j,
          fieldRoot (realizationData A hs hp b s) ℚ false i⁆⁆ := by
            simp only [Ring.lie_def]
            noncomm_ring
      _=0 := by rw [hh,neg_zero]
  exact sub_eq_zero.mp he

theorem collecting_bracket_cube (i j : Fin r) (hij : cartan b s i j= -1) :
    ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
      fieldRoot (realizationData A hs hp b s) ℚ false j⁆^3=0 :=
  pow_eq_zero_of_conjugate (parameterWeyl A hs hp b s ℚ i 1) _ _
    (weyl_conjugate_adjacent A hs hp b s i j hij) 3 (root_cube A hs hp b s j)

theorem collecting_sum_cube (i j : Fin r) (hij : cartan b s i j= -1) :
    (fieldRoot (realizationData A hs hp b s) ℚ false j+
      ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
        fieldRoot (realizationData A hs hp b s) ℚ false j⁆)^3=0 := by
  have hc := conjugate_adjacent A hs hp b s i j hij (1:ℚ)
  simp only [one_smul] at hc
  exact pow_eq_zero_of_conjugate (canonicalRoot (realizationData A hs hp b s) ℚ false i 1)
    _ _ hc 3 (root_cube A hs hp b s j)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCollectingPairCubes
