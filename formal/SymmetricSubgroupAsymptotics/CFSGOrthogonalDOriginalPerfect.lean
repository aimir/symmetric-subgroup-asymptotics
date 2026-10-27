import SymmetricSubgroupAsymptotics.CFSGSerreBaseChangePerfect
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalRootCandidates

/-! Every original D Cartan column has an actual minus-one neighbour.
The generic integral/tensor perfectness theorem therefore applies in
EVERY field, including characteristic two. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPerfect
open CFSG.Models.Chevalley
variable (r : ℕ) (hr : 4 ≤ r)

include hr in
theorem minus_one_neighbour (i : Fin r) : ∃ j : Fin r,CartanMatrix.D r j i = -1 := by
  have hil:=i.isLt
  by_cases hi : i.val+3 < r
  · let j : Fin r:=⟨i.val+1,by omega⟩
    refine ⟨j,?_⟩
    have hne : j ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      change i.val + 1 = i.val at hv
      omega
    have hn : ¬ r ≤ 2 := by omega
    have hforward : ¬ (j.val + 1 = i.val ∧ i.val + 2 < r) := by
      dsimp only [j]
      omega
    have hbackward : i.val + 1 = j.val ∧ j.val + 2 < r := by
      dsimp only [j]
      omega
    simp only [CartanMatrix.D,Matrix.of_apply,if_neg hne,if_neg hn,
      if_neg hforward,if_pos hbackward]
  · by_cases he : i.val+3=r
    · let j : Fin r:=⟨r-2,by omega⟩
      refine ⟨j,?_⟩
      simp only [CartanMatrix.D,Matrix.of_apply,Fin.ext_iff,j,Fin.val_mk]
      split_ifs <;> omega
    · let j : Fin r:=⟨r-3,by omega⟩
      refine ⟨j,?_⟩
      simp only [CartanMatrix.D,Matrix.of_apply,Fin.ext_iff,j,Fin.val_mk]
      split_ifs <;> omega

include hr in
theorem bracketSpan_eq_top (K : Type) [Field K] :
    Submodule.span K (Set.range (fun xy : Space (CartanMatrix.D r) K×Space (CartanMatrix.D r) K=>
      ⁅xy.1,xy.2⁆))=⊤ :=
  CFSGSerreBaseChangePerfect.bracketSpan_eq_top (CartanMatrix.D r) K (minus_one_neighbour r hr)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDOriginalPerfect
