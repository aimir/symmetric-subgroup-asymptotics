import SymmetricSubgroupAsymptotics.CFSGTwistedANaturalCartan
import SymmetricSubgroupAsymptotics.CFSGSquareZeroAdjoint
import SymmetricSubgroupAsymptotics.CFSGSerreGeneratorRepresentation

/-! The two Serre-power families for arbitrary rank A, proved by symbolic
matrix units. These install an actual representation of the original
rational Serre quotient, without any faithfulness assumption. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem A_offdiag_cases (i j : Fin r) (hij : i ≠ j) :
    CartanMatrix.A r i j = 0 ∨ CartanMatrix.A r i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij]
  split_ifs <;> simp

theorem positive_lie_of_cartan_zero (i j : Fin r) (hz : CartanMatrix.A r i j = 0) :
    ⁅positive R r i, positive R r j⁆ = 0 := by
  have hij : i ≠ j := by
    intro h
    subst j
    norm_num [CartanMatrix.A] at hz
  have hnear : ¬ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
    intro h
    simp only [CartanMatrix.A, Matrix.of_apply, if_neg hij, if_pos h] at hz
    norm_num at hz
  have hab : i.succ ≠ j.castSucc := by
    intro h
    apply hnear
    left
    exact congrArg (fun k : Fin (r + 1) => k.val) h
  have hba : j.succ ≠ i.castSucc := by
    intro h
    apply hnear
    right
    exact congrArg (fun k : Fin (r + 1) => k.val) h
  simp [positive, Ring.lie_def, hab, hba]

theorem positive_sandwich (i j : Fin r) :
    positive R r i * positive R r j * positive R r i = 0 := by
  have hbad : ¬ (j.castSucc = i.succ ∧ j.succ = i.castSucc) := by
    rintro ⟨h₁, h₂⟩
    have h₁v := congrArg (fun k : Fin (r + 1) => k.val) h₁
    have h₂v := congrArg (fun k : Fin (r + 1) => k.val) h₂
    change j.val = i.val + 1 at h₁v
    change j.val + 1 = i.val at h₂v
    omega
  have hmiddle : positive R r j i.succ i.castSucc = 0 := by
    simp [positive, Matrix.single, hbad]
  change Matrix.single i.castSucc i.succ (1 : R) * positive R r j *
    Matrix.single i.castSucc i.succ 1 = 0
  simp only [Matrix.single_mul_mul_single, hmiddle, mul_zero, zero_mul, Matrix.single_zero]

theorem positive_serre (i j : Fin r) :
    (LieAlgebra.ad R (Mat R r) (positive R r i) ^ (-CartanMatrix.A r i j).toNat)
      ⁅positive R r i, positive R r j⁆ = 0 := by
  by_cases hij : i = j
  · subst j
    rw [lie_self]
    exact map_zero _
  · rcases A_offdiag_cases r i j hij with hc | hc
    · rw [hc]
      change ⁅positive R r i, positive R r j⁆ = 0
      exact positive_lie_of_cartan_zero R r i j hc
    · rw [hc]
      change ⁅positive R r i, ⁅positive R r i, positive R r j⁆⁆ = 0
      have he : positive R r i * positive R r i = 0 := by
        simpa only [pow_two] using positive_sq_zero R r i
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he]
      simp only [positive_sandwich, add_zero, neg_zero]

theorem transpose_lie (X Y : Mat R r) :
    ⁅X, Y⁆.transpose = -⁅X.transpose, Y.transpose⁆ := by
  simp only [Ring.lie_def, Matrix.transpose_sub, Matrix.transpose_mul, neg_sub]

theorem negative_lie_of_cartan_zero (i j : Fin r) (hz : CartanMatrix.A r i j = 0) :
    ⁅negative R r i, negative R r j⁆ = 0 := by
  have hh := congrArg Matrix.transpose (positive_lie_of_cartan_zero R r i j hz)
  rw [transpose_lie, Matrix.transpose_zero] at hh
  exact neg_eq_zero.mp hh

theorem negative_sandwich (i j : Fin r) :
    negative R r i * negative R r j * negative R r i = 0 := by
  have hh := congrArg Matrix.transpose (positive_sandwich R r i j)
  simpa only [negative, Matrix.transpose_mul, Matrix.transpose_zero, mul_assoc] using hh

theorem negative_serre (i j : Fin r) :
    (LieAlgebra.ad R (Mat R r) (negative R r i) ^ (-CartanMatrix.A r i j).toNat)
      ⁅negative R r i, negative R r j⁆ = 0 := by
  by_cases hij : i = j
  · subst j
    rw [lie_self]
    exact map_zero _
  · rcases A_offdiag_cases r i j hij with hc | hc
    · rw [hc]
      change ⁅negative R r i, negative R r j⁆ = 0
      exact negative_lie_of_cartan_zero R r i j hc
    · rw [hc]
      change ⁅negative R r i, ⁅negative R r i, negative R r j⁆⁆ = 0
      have he : negative R r i * negative R r i = 0 := by
        simpa only [pow_two] using negative_sq_zero R r i
      rw [CFSGSquareZeroAdjoint.lie_lie _ _ he]
      simp only [negative_sandwich, add_zero, neg_zero]

def rationalNatural (r : ℕ) :
    CFSG.Models.Chevalley.RationalLie (CartanMatrix.A r) →ₗ⁅ℚ⁆ Mat ℚ r :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation
    (cartan ℚ r) (positive ℚ r) (negative ℚ r) (CartanMatrix.A r)
    (cartan_cartan ℚ r) (EF ℚ r) (HE ℚ r) (HF ℚ r)
    (positive_serre ℚ r) (negative_serre ℚ r)

@[simp] theorem rationalNatural_H (r : ℕ) (i : Fin r) :
    rationalNatural r (CFSG.Models.Chevalley.generator (CartanMatrix.A r)
      (CartanMatrix.Generators.H i)) = cartan ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rationalNatural_E (r : ℕ) (i : Fin r) :
    rationalNatural r (CFSG.Models.Chevalley.generator (CartanMatrix.A r)
      (CartanMatrix.Generators.E i)) = positive ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

@[simp] theorem rationalNatural_F (r : ℕ) (i : Fin r) :
    rationalNatural r (CFSG.Models.Chevalley.generator (CartanMatrix.A r)
      (CartanMatrix.Generators.F i)) = negative ℚ r i :=
  CFSGSerreGeneratorRepresentation.rationalRepresentation_generator _ _ _ _ _ _ _ _ _ _ _

end SymmetricSubgroupAsymptotics.CFSGTwistedANaturalMatrices
