import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralRealization

/-! Actual rational simple-root adjoint strings at Cartan entries zero
and minus one. The length-two relation is discharged by the original
Geck Serre theorem; it is not a new representation input. Integral
transport and higher-rank root collecting remain separate obligations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem rational_E_eq (i : Fin r) :
    fieldRoot (realizationData A hs hp b s) ℚ false i=E b s i := by
  change (Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.E b (s i))=
    RootPairing.GeckConstruction.e (s i)
  exact CFSGGeckIntegralMatrices.map_E b (s i)

theorem double_lie_of_cartan_neg_one (i j : Fin r) (hij : cartan b s i j= -1) :
    ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
      ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
        fieldRoot (realizationData A hs hp b s) ℚ false j⁆⁆=0 := by
  simp only [rational_E_eq]
  have hh := serreE b s i j
  simpa only [hij,neg_neg,Int.toNat_one,pow_one] using hh

theorem lie_of_cartan_zero (i j : Fin r) (hij : cartan b s i j=0) :
    ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
      fieldRoot (realizationData A hs hp b s) ℚ false j⁆=0 := by
  simp only [rational_E_eq]
  have hh := serreE b s i j
  simpa only [hij,neg_zero,Int.toNat_zero,pow_zero,Module.End.one_apply] using hh

theorem conjugate_adjacent (i j : Fin r) (hij : cartan b s i j= -1) (t : ℚ) :
    (canonicalRoot (realizationData A hs hp b s) ℚ false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) ℚ)*
      fieldRoot (realizationData A hs hp b s) ℚ false j*
      (((canonicalRoot (realizationData A hs hp b s) ℚ false i t)⁻¹ :
        (Matrix (b.support⊕Roots A) (b.support⊕Roots A) ℚ)ˣ) : Matrix
          (b.support⊕Roots A) (b.support⊕Roots A) ℚ)=
      fieldRoot (realizationData A hs hp b s) ℚ false j+
        t • ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
          fieldRoot (realizationData A hs hp b s) ℚ false j⁆ :=
  canonicalRoot_conjugation_of_double_lie (realizationData A hs hp b s) false i _
    (double_lie_of_cartan_neg_one A hs hp b s i j hij) t

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings
