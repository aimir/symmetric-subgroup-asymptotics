import SymmetricSubgroupAsymptotics.MarkedC4CoprimePhysicalGrid
import Mathlib.Algebra.Group.Action.End

/-! Compress actual permutation fibers by deleting singleton fibers.
Every action and its kernel are constructed from the original fibers. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActiveFiberPermutation

variable {I : Type} (F : I → Type)
abbrev Support := Σ i : I, {x : F i // Nat.card (F i)≠1}

variable {G : Type} [Group G] [∀ i, MulAction G (F i)]
instance supportAction : MulAction G (Support F) where
  smul g z := ⟨z.1,⟨g • z.2.1,z.2.2⟩⟩
  one_smul z := by
    rcases z with ⟨i,x,hx⟩
    change (⟨i,⟨1 • x,hx⟩⟩ : Support F)=⟨i,⟨x,hx⟩⟩
    simp only [one_smul]
  mul_smul g h z := by
    rcases z with ⟨i,x,hx⟩
    change (⟨i,⟨(g*h) • x,hx⟩⟩ : Support F)=⟨i,⟨g • (h • x),hx⟩⟩
    simp only [mul_smul]

def action : G →* Equiv.Perm (Support F) := MulAction.toPermHom G (Support F)

/-- Singleton removal loses no permutation information. -/
theorem fixes_iff (g : G) :
    (∀ z : Support F, g • z=z) ↔ ∀ i (x : F i), g • x=x := by
  constructor
  · intro h i x
    by_cases hi : Nat.card (F i)=1
    · haveI : Subsingleton (F i) := (Nat.card_eq_one_iff_unique.mp hi).1
      exact Subsingleton.elim _ _
    · have hz := h ⟨i,⟨x,hi⟩⟩
      change (⟨i,⟨g • x,hi⟩⟩ : Support F)=⟨i,⟨x,hi⟩⟩ at hz
      have hx : (⟨g • x,hi⟩ : {x : F i // Nat.card (F i)≠1})=⟨x,hi⟩ := by
        simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hz
      exact congrArg Subtype.val hx
  · intro h z
    rcases z with ⟨i,x,hx⟩
    change (⟨i,⟨g • x,hx⟩⟩ : Support F)=⟨i,⟨x,hx⟩⟩
    rw [h i x]

theorem ker_iff (g : G) : g∈(action (G := G) F).ker ↔
    ∀ i (x : F i), g • x=x := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    apply (fixes_iff F g).mp
    intro z
    exact congrArg (fun e : Equiv.Perm (Support F) => e z) h
  · intro h
    apply Equiv.ext
    exact (fixes_iff F g).mpr h

variable [Fintype I] [∀ i, Finite (F i)]
theorem card_support : Nat.card (Support F)=
    ∑ i, CoprimePhysicalGrid.activeDegree (Nat.card (F i)) := by
  rw [Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : Nat.card (F i)=1
  · simp [hi,CoprimePhysicalGrid.activeDegree]
  · simp [hi,CoprimePhysicalGrid.activeDegree]
end SymmetricSubgroupAsymptotics.MarkedC4.ActiveFiberPermutation
