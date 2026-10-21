import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices

/-! Actual diagonal coroots of the B-transpose natural matrices. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem cartan_eq (i : Fin r) : cartan R r i=
    if h : i.val+1<r then
      (Matrix.single (pos r i) (pos r i) 1+
        Matrix.single (neg r (⟨i.val+1,h⟩ : Fin r)) (neg r (⟨i.val+1,h⟩ : Fin r)) 1)-
      (Matrix.single (pos r (⟨i.val+1,h⟩ : Fin r)) (pos r (⟨i.val+1,h⟩ : Fin r)) 1+
        Matrix.single (neg r i) (neg r i) 1)
    else Matrix.single (pos r i) (pos r i) 2-Matrix.single (neg r i) (neg r i) 2 := by
  by_cases h : i.val+1<r
  · simp [cartan,positive,negative,h,Ring.lie_def,sub_mul,mul_sub]
  · simp [cartan,positive,negative,h,Ring.lie_def,sub_mul,mul_sub,pos,neg,middle] <;> abel

theorem cartan_isDiagonal (i : Fin r) :
    ∃d : Index r→R,cartan R r i=Matrix.diagonal d := by
  rw [cartan_eq]
  split_ifs
  all_goals
    simp only [←Matrix.diagonal_single,Matrix.diagonal_add,Matrix.diagonal_sub]
    exact ⟨_,rfl⟩

theorem cartan_cartan (i j : Fin r) : ⁅cartan R r i,cartan R r j⁆=0 := by
  obtain ⟨d,hd⟩ := cartan_isDiagonal R r i
  obtain ⟨e,he⟩ := cartan_isDiagonal R r j
  simp only [hd,he,Ring.lie_def,Matrix.diagonal_mul_diagonal]
  have hde : (fun x=>d x*e x)=(fun x=>e x*d x) := by funext x;exact mul_comm _ _
  rw [hde,sub_self]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBSerreMatrices
