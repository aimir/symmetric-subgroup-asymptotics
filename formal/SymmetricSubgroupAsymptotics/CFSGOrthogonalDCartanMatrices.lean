import SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
import Mathlib.Tactic.Abel

/-! The literal natural D coroots are diagonal. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
variable (R : Type*) [CommRing R] (r : ℕ)

theorem cartan_eq (hr : 4≤r) (i : Fin r) : cartan R r i=
    if h : i.val+1<r then
      (Matrix.single (Sum.inl i) (Sum.inl i) 1+
        Matrix.single (Sum.inr (⟨i.val+1,h⟩ : Fin r)) (Sum.inr (⟨i.val+1,h⟩ : Fin r)) 1)-
      (Matrix.single (Sum.inl (⟨i.val+1,h⟩ : Fin r)) (Sum.inl (⟨i.val+1,h⟩ : Fin r)) 1+
        Matrix.single (Sum.inr i) (Sum.inr i) 1)
    else
      (Matrix.single (Sum.inl (previous r i)) (Sum.inl (previous r i)) 1+
        Matrix.single (Sum.inl i) (Sum.inl i) 1)-
      (Matrix.single (Sum.inr (previous r i)) (Sum.inr (previous r i)) 1+
        Matrix.single (Sum.inr i) (Sum.inr i) 1) := by
  by_cases hi : i.val+1<r
  · have hn : (⟨i.val+1,hi⟩ : Fin r)≠i := by
      intro he
      have hv := congrArg Fin.val he
      change i.val+1=i.val at hv
      omega
    simp [cartan,positive,negative,hi,Ring.lie_def,Matrix.transpose_sub,Matrix.transpose_single,
      sub_mul,mul_sub,hn,hn.symm]
  · have hn := previous_ne_of_last r hr i hi
    simp [cartan,positive,negative,hi,Ring.lie_def,Matrix.transpose_sub,Matrix.transpose_single,
      sub_mul,mul_sub,hn,hn.symm] <;> abel

theorem cartan_isDiagonal (hr : 4≤r) (i : Fin r) :
    ∃d : Index r→R,cartan R r i=Matrix.diagonal d := by
  rw [cartan_eq R r hr]
  split_ifs
  all_goals
    simp only [←Matrix.diagonal_single,Matrix.diagonal_add,Matrix.diagonal_sub]
    exact ⟨_,rfl⟩

theorem cartan_cartan (hr : 4≤r) (i j : Fin r) : ⁅cartan R r i,cartan R r j⁆=0 := by
  obtain ⟨d,hd⟩ := cartan_isDiagonal R r hr i
  obtain ⟨e,he⟩ := cartan_isDiagonal R r hr j
  simp only [hd,he,Ring.lie_def,Matrix.diagonal_mul_diagonal]
  have hde : (fun x => d x*e x)=(fun x => e x*d x) := by funext x;exact mul_comm _ _
  rw [hde,sub_self]

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDSerreMatrices
