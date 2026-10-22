import Mathlib.Data.Matrix.Cartan
import Mathlib.Logic.Relation
import Mathlib.Tactic.FinCases

/-! Explicit paths in the three literal exceptional simply-laced Cartan graphs. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalCartanConnected

private theorem connected_of_zero {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℤ)
    (hs : A.transpose=A)
    (h : ∀ i,Relation.ReflTransGen (fun a b=>A a b≠0) 0 i) :
    ∀ i j,Relation.ReflTransGen (fun a b=>A a b≠0) i j := by
  have hr : Symmetric (fun a b=>A a b≠0) := by
    intro a b hab
    have he := congrFun (congrFun hs a) b
    change A b a=A a b at he
    rwa [he]
  intro i j
  exact ((Relation.ReflTransGen.symmetric hr) (h i)).trans (h j)

theorem E8_connected : ∀ i j,
    Relation.ReflTransGen (fun a b=>CartanMatrix.E₈ a b≠0) i j := by
  apply connected_of_zero CartanMatrix.E₈ CartanMatrix.E₈_transpose
  have h0 : Relation.ReflTransGen (fun a b=>CartanMatrix.E₈ a b≠0) 0 0 := .refl
  have h2 := h0.tail (by decide : CartanMatrix.E₈ 0 2≠0)
  have h3 := h2.tail (by decide : CartanMatrix.E₈ 2 3≠0)
  have h1 := h3.tail (by decide : CartanMatrix.E₈ 3 1≠0)
  have h4 := h3.tail (by decide : CartanMatrix.E₈ 3 4≠0)
  have h5 := h4.tail (by decide : CartanMatrix.E₈ 4 5≠0)
  have h6 := h5.tail (by decide : CartanMatrix.E₈ 5 6≠0)
  have h7 := h6.tail (by decide : CartanMatrix.E₈ 6 7≠0)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7

theorem E7_connected : ∀ i j,
    Relation.ReflTransGen (fun a b=>CartanMatrix.E₇ a b≠0) i j := by
  apply connected_of_zero CartanMatrix.E₇ CartanMatrix.E₇_transpose
  have h0 : Relation.ReflTransGen (fun a b=>CartanMatrix.E₇ a b≠0) 0 0 := .refl
  have h2 := h0.tail (by decide : CartanMatrix.E₇ 0 2≠0)
  have h3 := h2.tail (by decide : CartanMatrix.E₇ 2 3≠0)
  have h1 := h3.tail (by decide : CartanMatrix.E₇ 3 1≠0)
  have h4 := h3.tail (by decide : CartanMatrix.E₇ 3 4≠0)
  have h5 := h4.tail (by decide : CartanMatrix.E₇ 4 5≠0)
  have h6 := h5.tail (by decide : CartanMatrix.E₇ 5 6≠0)
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6

theorem E6_connected : ∀ i j,
    Relation.ReflTransGen (fun a b=>CartanMatrix.E₆ a b≠0) i j := by
  apply connected_of_zero CartanMatrix.E₆ CartanMatrix.E₆_transpose
  have h0 : Relation.ReflTransGen (fun a b=>CartanMatrix.E₆ a b≠0) 0 0 := .refl
  have h2 := h0.tail (by decide : CartanMatrix.E₆ 0 2≠0)
  have h3 := h2.tail (by decide : CartanMatrix.E₆ 2 3≠0)
  have h1 := h3.tail (by decide : CartanMatrix.E₆ 3 1≠0)
  have h4 := h3.tail (by decide : CartanMatrix.E₆ 3 4≠0)
  have h5 := h4.tail (by decide : CartanMatrix.E₆ 4 5≠0)
  intro i
  fin_cases i <;> first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4 | exact h5

end SymmetricSubgroupAsymptotics.CFSGExceptionalCartanConnected
