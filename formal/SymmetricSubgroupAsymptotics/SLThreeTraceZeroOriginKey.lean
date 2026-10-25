import SymmetricSubgroupAsymptotics.SLThreeNonzeroKeyClassBound
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Group

/-! Two literal conjugacy invariants identify the origin cyclic key in
characteristic two. Both traces vanish only at that key; the noncyclic
keys are excluded by their actual determinant-one condition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.SLThreeTraceZeroOriginKey
open SLThreeNormalFormCover
variable {K : Type*} [Field K] [CharP K 2]

theorem matrixKey_eq_origin (A : Matrix.SpecialLinearGroup (Fin 3) K)
    (ht : A.val.trace=0) (hi : (A⁻¹).val.trace=0) :
    SLThreeConjugacyClassBound.matrixKey K A=Sum.inl (0,0) := by
  let k := SLThreeConjugacyClassBound.matrixKey K A
  have hd : (normalMatrix K k).det=1 := SLThreeNonzeroKeyClassBound.selected_key_det K A
  let B : Matrix.SpecialLinearGroup (Fin 3) K := ⟨normalMatrix K k,hd⟩
  obtain ⟨P,hP⟩ := SLThreeConjugacyClassBound.exists_conjugator_for_key K A
  have hGL : P⁻¹*Matrix.SpecialLinearGroup.toGL A*P=Matrix.SpecialLinearGroup.toGL B := by
    apply Units.ext
    exact hP
  have hInv : P⁻¹*Matrix.SpecialLinearGroup.toGL (A⁻¹)*P=
      Matrix.SpecialLinearGroup.toGL (B⁻¹) := by
    simp only [map_inv]
    rw [←hGL]
    group
  have hInvMat : (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K)*(A⁻¹).val*
      (P : Matrix (Fin 3) (Fin 3) K)=(B⁻¹).val :=
    congrArg (fun g : Matrix.GeneralLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) hInv
  have htN : (normalMatrix K k).trace=0 := by
    rw [←hP,Matrix.trace_units_conj']
    exact ht
  have hiN : (Matrix.adjugate (normalMatrix K k)).trace=0 := by
    change (B⁻¹).val.trace=0
    rw [←hInvMat,Matrix.trace_units_conj']
    exact hi
  change k=Sum.inl (0,0)
  cases he : k with
  | inl st =>
    rcases st with ⟨s,t⟩
    have ht' : t=0 := by
      simpa [he,normalMatrix,FiniteThreeCyclicCompanion.companion,Matrix.trace,
        Fin.sum_univ_three] using htN
    have hs' : s=0 := by
      simpa [he,normalMatrix,FiniteThreeCyclicCompanion.companion,Matrix.adjugate_fin_three,
        Matrix.trace,Fin.sum_univ_three,CharTwo.neg_eq] using hiN
    simp only [hs',ht']
  | inr u =>
    cases u with
    | inl a =>
      have haInv : (a⁻¹)^2=0 := by
        simpa [he,normalMatrix,FiniteThreeNoncyclicConjugacy.diagonal,Matrix.trace,
          Fin.sum_univ_three,CharTwo.add_self_eq_zero] using htN
      have ha : a=0 := inv_eq_zero.mp ((pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp haInv)
      have hbad : (0 : K)=1 := by
        simpa [he,normalMatrix,diagonal_det,ha] using hd
      exact False.elim (zero_ne_one hbad)
    | inr a =>
      have ha : a=0 := by
        simpa [he,normalMatrix,FiniteThreeNoncyclicConjugacy.jordan,Matrix.trace,
          Fin.sum_univ_three,CharTwo.add_self_eq_zero] using htN
      have hbad : (0 : K)=1 := by
        simpa [he,normalMatrix,FiniteThreeNoncyclicConjugacy.jordan,Matrix.det_fin_three,ha] using hd
      exact False.elim (zero_ne_one hbad)

theorem exists_origin_conjugator (A : Matrix.SpecialLinearGroup (Fin 3) K)
    (ht : A.val.trace=0) (hi : (A⁻¹).val.trace=0) :
    ∃ P : Matrix.GeneralLinearGroup (Fin 3) K,
      (↑(P⁻¹) : Matrix (Fin 3) (Fin 3) K)*A.val*(P : Matrix (Fin 3) (Fin 3) K)=
        FiniteThreeCyclicCompanion.companion ![1,0,0] := by
  obtain ⟨P,hP⟩ := SLThreeConjugacyClassBound.exists_conjugator_for_key K A
  rw [matrixKey_eq_origin A ht hi] at hP
  exact ⟨P,hP⟩

end SymmetricSubgroupAsymptotics.SLThreeTraceZeroOriginKey
