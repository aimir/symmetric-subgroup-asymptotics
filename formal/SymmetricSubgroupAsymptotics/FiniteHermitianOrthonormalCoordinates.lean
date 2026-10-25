import SymmetricSubgroupAsymptotics.FiniteHermitianBasisCoordinates
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan

/-! A literal orthonormal basis identifies the preserved matrix pairing
with its coordinate pairing. This is an algebraic transport identity;
existence of the basis and all cardinal bounds remain separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalCoordinates
open Module CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
open FiniteHermitianBasisCoordinates

variable {K I : Type*} [Field K] [Fintype I]
    (sigma : K ≃+* K) (H : Matrix I I K)

private theorem pair_smul_left (a : K) (x y : I → K) :
    hermitianPair sigma H (a • x) y=sigma a*hermitianPair sigma H x y := by
  simpa only [one_smul,mul_one] using hermitianPair_smul sigma H a 1 x y

private theorem pair_smul_right (a : K) (x y : I → K) :
    hermitianPair sigma H x (a • y)=a*hermitianPair sigma H x y := by
  simpa only [one_smul,map_one,one_mul] using hermitianPair_smul sigma H 1 a x y

private theorem pair_sum_left {J : Type*} (s : Finset J) (f : J → I → K) (y : I → K) :
    hermitianPair sigma H (∑ j ∈ s, f j) y=∑ j ∈ s, hermitianPair sigma H (f j) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,pair_zero_left]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj,hermitianPair_add_left,ih,Finset.sum_insert hj]

private theorem pair_sum_right {J : Type*} (s : Finset J) (f : J → I → K) (x : I → K) :
    hermitianPair sigma H x (∑ j ∈ s, f j)=∑ j ∈ s, hermitianPair sigma H x (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,pair_zero_right]
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj,hermitianPair_add_right,ih,Finset.sum_insert hj]

theorem pairing_basis_left {n : ℕ} (b : Basis (Fin n) K (I → K))
    (hb : ∀ i j, hermitianPair sigma H (b i) (b j)=if i=j then 1 else 0)
    (i : Fin n) (x : I → K) : hermitianPair sigma H (b i) x=b.repr x i := by
  classical
  calc
    _ = hermitianPair sigma H (b i) (∑ j : Fin n, b.repr x j • b j) :=
      congrArg (fun y => hermitianPair sigma H (b i) y) (b.sum_repr x).symm
    _ = ∑ j : Fin n, hermitianPair sigma H (b i) (b.repr x j • b j) :=
      pair_sum_right sigma H Finset.univ _ _
    _ = _ := by
      simp only [pair_smul_right,hb]
      simp

theorem pairing_eq_coordinatePair {n : ℕ} (b : Basis (Fin n) K (I → K))
    (hb : ∀ i j, hermitianPair sigma H (b i) (b j)=if i=j then 1 else 0)
    (x y : I → K) : hermitianPair sigma H x y=coordinatePair sigma b x y := by
  classical
  calc
    _ = hermitianPair sigma H (∑ i : Fin n, b.repr x i • b i) y :=
      congrArg (fun z => hermitianPair sigma H z y) (b.sum_repr x).symm
    _ = ∑ i : Fin n, hermitianPair sigma H (b.repr x i • b i) y :=
      pair_sum_left sigma H Finset.univ _ _
    _ = ∑ i : Fin n, sigma (b.repr x i)*hermitianPair sigma H (b i) y := by
      simp only [pair_smul_left]
    _ = _ := by
      simp only [pairing_basis_left sigma H b hb]
      rfl

end SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalCoordinates
