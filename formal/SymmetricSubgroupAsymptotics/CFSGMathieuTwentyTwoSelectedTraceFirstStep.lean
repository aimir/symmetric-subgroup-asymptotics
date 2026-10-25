import SymmetricSubgroupAsymptotics.External.CFSG.Models.Mathieu22

/-! The first five literal letter transitions of the ONLY selected M22
word `a³ b²` at point zero. The bounded primary diagnostic recorded
`0,17,10,18,1,14`; every entry is checked below from the pinned cycles.
No full action table, group closure, or other selected word is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedTraceFirstStep
open CFSG.Models.Mathieu22Construction

/-- The single selected word, with multiplication acting right to left. -/
def selectedWord : Equiv.Perm (Fin 22) := a ^ 3 * b ^ 2

private theorem b_apply_first (x : Fin 22)
    (h1 : x ∉ ([2,14] : List (Fin 22)))
    (h2 : x ∉ ([4,7,6,15] : List (Fin 22)))
    (h3 : x ∉ ([5,21,12,13,9,11,16,20] : List (Fin 22))) :
    b x = List.formPerm ([0,17,10,19,18,8,3,1] : List (Fin 22)) x := by
  simp only [b, Equiv.Perm.mul_apply, List.formPerm_apply_of_notMem h3,
    List.formPerm_apply_of_notMem h2, List.formPerm_apply_of_notMem h1]

private theorem a_apply_second (x y : Fin 22)
    (h3 : x ∉ ([3,13,9,19,20] : List (Fin 22)))
    (h2 : x ∉ ([2,7,8,16,12] : List (Fin 22)))
    (h1 : List.formPerm ([1,14,21,10,18] : List (Fin 22)) x = y)
    (h0 : y ∉ ([0,11,4,5,15] : List (Fin 22))) : a x = y := by
  simp only [a, Equiv.Perm.mul_apply, List.formPerm_apply_of_notMem h3,
    List.formPerm_apply_of_notMem h2, h1, List.formPerm_apply_of_notMem h0]

private theorem b_zero : b (0 : Fin 22) = 17 := by
  apply (b_apply_first 0 (by decide) (by decide) (by decide)).trans
  exact List.formPerm_apply_lt_getElem
    ([0,17,10,19,18,8,3,1] : List (Fin 22)) (by decide) 0 (by decide)

private theorem b_seventeen : b (17 : Fin 22) = 10 := by
  apply (b_apply_first 17 (by decide) (by decide) (by decide)).trans
  exact List.formPerm_apply_lt_getElem
    ([0,17,10,19,18,8,3,1] : List (Fin 22)) (by decide) 1 (by decide)

private theorem a_ten : a (10 : Fin 22) = 18 := by
  apply a_apply_second 10 18 (by decide) (by decide) _ (by decide)
  exact List.formPerm_apply_lt_getElem
    ([1,14,21,10,18] : List (Fin 22)) (by decide) 3 (by decide)

private theorem a_eighteen : a (18 : Fin 22) = 1 := by
  apply a_apply_second 18 1 (by decide) (by decide) _ (by decide)
  exact List.formPerm_apply_getElem
    ([1,14,21,10,18] : List (Fin 22)) (by decide) 4 (by decide)

private theorem a_one : a (1 : Fin 22) = 14 := by
  apply a_apply_second 1 14 (by decide) (by decide) _ (by decide)
  exact List.formPerm_apply_lt_getElem
    ([1,14,21,10,18] : List (Fin 22)) (by decide) 0 (by decide)

/-- The first recorded whole-word transition, certified from its five
actual pinned cycle applications. -/
theorem first_step : selectedWord (0 : Fin 22) = 14 := by
  simp only [selectedWord, pow_succ, pow_zero, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, b_zero, b_seventeen, a_ten, a_eighteen, a_one]

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSelectedTraceFirstStep
