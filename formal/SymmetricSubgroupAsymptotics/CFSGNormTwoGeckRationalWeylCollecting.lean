import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalAdjointStrings
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedWeyl
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticAdjointWeylString

/-! Actual adjacent Weyl collecting, with three opaque Lie identities
separated from the abstract adjoint-string calculation. The original
EF/HE/Serre identities discharge every string input. This is rational;
integer/root-word collecting is not inferred without explicit transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckParameterizedWeyl
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem rational_F_eq (i : Fin r) :
    fieldRoot (realizationData A hs hp b s) ℚ true i=F b s i := by
  change (Int.castRingHom ℚ).mapMatrix (CFSGGeckIntegralMatrices.F b (s i))=
    RootPairing.GeckConstruction.f (s i)
  exact CFSGGeckIntegralMatrices.map_F b (s i)

theorem indices_ne_of_cartan_neg_one (i j : Fin r) (hij : cartan b s i j= -1) : i≠j := by
  intro h
  subst j
  have hd := b.cartanMatrix_apply_same (s i)
  change cartan b s i i=2 at hd
  omega

theorem F_E_ne (i j : Fin r) (hne : i≠j) :
    ⁅fieldRoot (realizationData A hs hp b s) ℚ true i,
      fieldRoot (realizationData A hs hp b s) ℚ false j⁆=0 := by
  rw [rational_F_eq,rational_E_eq]
  calc
    ⁅F b s i,E b s j⁆= -⁅E b s j,F b s i⁆ := (lie_skew _ _).symm
    _=0 := by rw [EF,if_neg (Ne.symm hne),neg_zero]

theorem F_EE_adjacent (i j : Fin r) (hij : cartan b s i j= -1) :
    ⁅fieldRoot (realizationData A hs hp b s) ℚ true i,
      ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
        fieldRoot (realizationData A hs hp b s) ℚ false j⁆⁆=
      fieldRoot (realizationData A hs hp b s) ℚ false j := by
  simp only [rational_F_eq,rational_E_eq]
  have hself : ⁅F b s i,E b s i⁆= -H b s i := by
    calc
      ⁅F b s i,E b s i⁆= -⁅E b s i,F b s i⁆ := (lie_skew _ _).symm
      _= -H b s i := by rw [EF,if_pos rfl]
  have hother : ⁅F b s i,E b s j⁆=0 := by
    calc
      ⁅F b s i,E b s j⁆= -⁅E b s j,F b s i⁆ := (lie_skew _ _).symm
      _=0 := by rw [EF,if_neg (Ne.symm (indices_ne_of_cartan_neg_one A hs hp b s i j hij)),neg_zero]
  rw [leibniz_lie,hself,hother,lie_zero,add_zero,neg_lie,HE,hij]
  simp

theorem weyl_conjugate_adjacent (i j : Fin r) (hij : cartan b s i j= -1) :
    (parameterWeyl A hs hp b s ℚ i 1 : Target b)*
      fieldRoot (realizationData A hs hp b s) ℚ false j*
        (((parameterWeyl A hs hp b s ℚ i 1)⁻¹ : (Target b)ˣ) : Target b)=
      ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
        fieldRoot (realizationData A hs hp b s) ℚ false j⁆ := by
  have hh := CFSGSerreQuadraticAdjointWeylString.weyl_on_pair
    (realizationData A hs hp b s) i (fieldRoot (realizationData A hs hp b s) ℚ false j)
    ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
      fieldRoot (realizationData A hs hp b s) ℚ false j⁆ rfl
    (double_lie_of_cartan_neg_one A hs hp b s i j hij)
    (F_E_ne A hs hp b s i j (indices_ne_of_cartan_neg_one A hs hp b s i j hij))
    (F_EE_adjacent A hs hp b s i j hij)
  simpa only [parameterWeyl,canonicalWeyl,Units.val_one,inv_one] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalWeylCollecting
