import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckQuadratic

/-! Actual cubic and quadratic-coefficient annihilation for norm-two Geck
roots. These are matrix identities on the specified representation, prior
to the separate same-Lie-image fourth-coefficient assertion. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTruncation
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckColumns CFSGNormTwoGeckQuadratic
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    (b : (rootPairing A hs hp).Base)

theorem E_mul_second (i : b.support) :
    RootPairing.GeckConstruction.e i*secondMatrix A hs hp b i=0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [←Matrix.mulVec_mulVec,second_on_basis,Matrix.zero_mulVec]
  split_ifs
  · exact E_v_self A hs hp b i
  · exact Matrix.mulVec_zero _

theorem second_mul_E (i : b.support) :
    secondMatrix A hs hp b i*RootPairing.GeckConstruction.e i=0 := by
  have he : (2:ℚ) • (secondMatrix A hs hp b i*RootPairing.GeckConstruction.e i)=0 := by
    calc
      (2:ℚ) • (secondMatrix A hs hp b i*RootPairing.GeckConstruction.e i)=
          ((2:ℚ) • secondMatrix A hs hp b i)*RootPairing.GeckConstruction.e i := by
        rw [smul_mul_assoc]
      _=(RootPairing.GeckConstruction.e i)^2*RootPairing.GeckConstruction.e i := by rw [E_square]
      _=RootPairing.GeckConstruction.e i*(RootPairing.GeckConstruction.e i)^2 := by
        simp only [pow_two,mul_assoc]
      _=RootPairing.GeckConstruction.e i*((2:ℚ) • secondMatrix A hs hp b i) := by rw [E_square]
      _=(2:ℚ) • (RootPairing.GeckConstruction.e i*secondMatrix A hs hp b i) := by
        rw [mul_smul_comm]
      _=0 := by rw [E_mul_second,smul_zero]
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

theorem E_cube (i : b.support) : (RootPairing.GeckConstruction.e i)^3=0 := by
  rw [show (3:ℕ)=2+1 by rfl,pow_succ,E_square,smul_mul_assoc,second_mul_E,smul_zero]

theorem second_square (i : b.support) : (secondMatrix A hs hp b i)^2=0 := by
  have he : (2:ℚ) • (secondMatrix A hs hp b i)^2=0 := by
    calc
      (2:ℚ) • (secondMatrix A hs hp b i)^2=
          ((2:ℚ) • secondMatrix A hs hp b i)*secondMatrix A hs hp b i := by
        rw [pow_two,smul_mul_assoc]
      _=(RootPairing.GeckConstruction.e i)^2*secondMatrix A hs hp b i := by rw [E_square]
      _=RootPairing.GeckConstruction.e i*
          (RootPairing.GeckConstruction.e i*secondMatrix A hs hp b i) := by
        rw [pow_two,mul_assoc]
      _=0 := by rw [E_mul_second,mul_zero]
  exact (smul_eq_zero.mp he).resolve_left (by norm_num)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckTruncation
