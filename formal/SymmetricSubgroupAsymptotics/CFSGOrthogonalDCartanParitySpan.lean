import SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanParityLattice
import Mathlib.Tactic.Abel

/-! The literal natural D Cartan columns span EXACTLY the even-sum
integer diagonal lattice. The proof uses chain telescoping and one
terminal sum root, without a rank-dependent determinant certificate. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanParitySpan
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDCartanParityLattice
variable (r : ℕ)

def unit (i : Fin r) : Fin r→ℤ := Pi.single i 1

theorem column_eq (hr : 4 ≤ r) (i : Fin r) : column r i=
    if h : i.val+1 < r then unit r i-unit r ⟨i.val+1,h⟩
    else unit r (previous r i)+unit r i := by
  funext j
  simp only [column,cartan_eq ℤ r hr]
  split_ifs <;> simp [unit,Matrix.add_apply,Matrix.sub_apply,Matrix.single_apply,Pi.single_apply,eq_comm]

private theorem difference_last_mem (hr : 4 ≤ r) (i : Fin r) :
    unit r i-unit r ⟨r-1,by omega⟩∈Submodule.span ℤ (Set.range (column r)) := by
  let last : Fin r:=⟨r-1,by omega⟩
  suffices h : ∀ n : ℕ,∀ i : Fin r,r-1-i.val=n→
      unit r i-unit r last∈Submodule.span ℤ (Set.range (column r)) by exact h _ i rfl
  intro n
  induction n with
  | zero =>
    intro i hi
    have he : i=last := by apply Fin.ext; dsimp [last]; have h:=i.isLt; omega
    rw [he,sub_self]
    exact Submodule.zero_mem _
  | succ n ih =>
    intro i hi
    have hn : i.val+1 < r := by have h:=i.isLt; omega
    let next : Fin r:=⟨i.val+1,hn⟩
    have hnext:=ih next (by dsimp [next]; omega)
    have hc : column r i=unit r i-unit r next := by rw [column_eq r hr,dif_pos hn]
    have he : unit r i-unit r last=column r i+(unit r next-unit r last) := by rw [hc]; abel
    rw [he]
    exact Submodule.add_mem _ (Submodule.subset_span ⟨i,rfl⟩) hnext

private theorem twice_last_mem (hr : 4 ≤ r) :
    (2:ℤ) • unit r ⟨r-1,by omega⟩∈Submodule.span ℤ (Set.range (column r)) := by
  let last : Fin r:=⟨r-1,by omega⟩
  let prev : Fin r:=⟨r-2,by omega⟩
  have hl : ¬last.val+1 < r := by dsimp [last]; omega
  have hp : prev.val+1 < r := by dsimp [prev]; omega
  have he : (⟨prev.val+1,hp⟩ : Fin r)=last := by apply Fin.ext; dsimp [prev,last]; omega
  have he' : previous r last=prev := by apply Fin.ext; dsimp [previous,last,prev]; omega
  have hc : (2:ℤ) • unit r last=column r last-column r prev := by
    rw [column_eq r hr,dif_neg hl,he',column_eq r hr,dif_pos hp,he]
    simp only [two_smul]
    abel
  rw [hc]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨last,rfl⟩)
    (Submodule.subset_span ⟨prev,rfl⟩)

theorem span_columns_eq_evenSum (hr : 4 ≤ r) :
    Submodule.span ℤ (Set.range (column r))=evenSum r := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro a ⟨i,rfl⟩
    exact column_mem r hr i
  · intro a ha
    obtain ⟨z,hz⟩:=ha
    let last : Fin r:=⟨r-1,by omega⟩
    have ha' : (∑ i : Fin r,a i • unit r i)=a := by
      classical
      funext j
      simp [unit,Finset.sum_apply,Pi.single_apply]
    have he : a=(∑ i : Fin r,a i • (unit r i-unit r last))+
        z • ((2:ℤ) • unit r last) := by
      simp only [smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,ha',hz,smul_smul]
      rw [mul_comm z 2]
      abel
    rw [he]
    apply Submodule.add_mem
    · apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (difference_last_mem r hr i)
    · exact Submodule.smul_mem _ z (twice_last_mem r hr)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDCartanParitySpan
