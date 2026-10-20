import SymmetricSubgroupAsymptotics.MarkedC4LiteralSolubleOrbitContainers
import Mathlib.Data.Nat.Factorial.Basic

/-! Ordinary published container inputs and the size of the constructed
container family. Roney--Dougal--Tracey Theorem 8.6(i), p.34 of v1, cites
Pyber [16, Lemma 3.2] for fewer than 2^(13 n) conjugacy classes of maximal
transitive soluble subgroups. The finite representative formulation below
states precisely that unmarked class bound; the empty action has its unique
representative. This is not a hypothesis giving a cover of original groups.
That cover was constructed in `LiteralSolubleOrbitContainers`.

The labelled local count pays at most n! conjugates. Fibre sizes sum to the
original degree, so the whole labelled orbit-container menu has only
2^O(n log(n+2)) entries. No marked parameter occurs in the menu. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators Pointwise
namespace SymmetricSubgroupAsymptotics.MarkedC4.SolubleContainerCount
open LiteralSolubleOrbitContainers

/-- The ordinary conjugacy-class statement of RDT Theorem 8.6(i). -/
def PublishedTheorem86Representatives : Prop :=
  ∀ (X : Type) [Fintype X], ∃ S : Finset (LocalContainer X),
    S.card ≤ 2^(13*Fintype.card X) ∧
      ∀ D : LocalContainer X, ∃ E ∈ S, ∃ p : Equiv.Perm X,
        D.val = (MulAut.conj p) • E.val

theorem local_card_bound (h86 : PublishedTheorem86Representatives)
    (X : Type) [Fintype X] :
    Nat.card (LocalContainer X) ≤ 2^(13*Fintype.card X) * (Fintype.card X).factorial := by
  obtain ⟨S,hS,hcover⟩ := h86 X
  choose representative hmem permutation heq using hcover
  let code : LocalContainer X → {E : LocalContainer X // E ∈ S} × Equiv.Perm X :=
    fun D => (⟨representative D,hmem D⟩,permutation D)
  have hc : Function.Injective code := by
    intro D E h
    have hr : representative D = representative E :=
      congrArg (fun z : {E : LocalContainer X // E ∈ S} × Equiv.Perm X => z.1.val) h
    have hp : permutation D = permutation E := congrArg Prod.snd h
    apply Subtype.ext
    rw [heq D,heq E,hr,hp]
  calc
    Nat.card (LocalContainer X) ≤ Nat.card ({E : LocalContainer X // E ∈ S} × Equiv.Perm X) :=
      Nat.card_le_card_of_injective code hc
    _ = S.card * (Fintype.card X).factorial := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_coe,Fintype.card_perm]
    _ ≤ 2^(13*Fintype.card X) * (Fintype.card X).factorial := Nat.mul_le_mul_right _ hS

variable (X : Type) [Fintype X]

/-- Actual original-point partitions and actual local maximal containers. -/
abbrev Index := Σ label : X → X, ∀ i : X, LocalContainer (Fiber label i)

local instance : Fintype (Index X) := Fintype.ofFinite _
local instance (label : X → X) (i : X) : Fintype (LocalContainer (Fiber label i)) :=
  Fintype.ofFinite _

theorem fiber_sum (label : X → X) :
    ∑ i : X, Fintype.card (Fiber label i) = Fintype.card X := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv label)

theorem fiber_card_le (label : X → X) (i : X) :
    Fintype.card (Fiber label i) ≤ Fintype.card X :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

theorem local_menu_product_bound (h86 : PublishedTheorem86Representatives)
    (label : X → X) :
    (∏ i : X, Fintype.card (LocalContainer (Fiber label i))) ≤
      2^(13*Fintype.card X) * (Fintype.card X+1)^(Fintype.card X) := by
  have hlocal (i : X) : Fintype.card (LocalContainer (Fiber label i)) ≤
      2^(13*Fintype.card (Fiber label i)) *
        (Fintype.card X+1)^(Fintype.card (Fiber label i)) := by
    have h := local_card_bound h86 (Fiber label i)
    rw [Nat.card_eq_fintype_card] at h
    exact h.trans (Nat.mul_le_mul_left _
      ((Nat.factorial_le_pow _).trans
        (Nat.pow_le_pow_left (Nat.le_succ_of_le (fiber_card_le X label i)) _)))
  calc
    _ ≤ ∏ i : X, (2^(13*Fintype.card (Fiber label i)) *
        (Fintype.card X+1)^(Fintype.card (Fiber label i))) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun i _ => hlocal i)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,
        Finset.prod_pow_eq_pow_sum,← Finset.mul_sum,fiber_sum]

/-- The orbit-label menu is counted once, independently of relative tuple
length and all global C4 marks. -/
theorem index_card_bound (h86 : PublishedTheorem86Representatives) :
    Nat.card (Index X) ≤ (Fintype.card X)^(Fintype.card X) *
      (2^(13*Fintype.card X) * (Fintype.card X+1)^(Fintype.card X)) := by
  change Nat.card (Σ label : X → X, ∀ i : X, LocalContainer (Fiber label i)) ≤ _
  rw [Nat.card_sigma]
  calc
    _ ≤ ∑ _label : X → X, (2^(13*Fintype.card X) *
        (Fintype.card X+1)^(Fintype.card X)) := by
      apply Finset.sum_le_sum
      intro label _
      simpa only [Nat.card_eq_fintype_card,Fintype.card_pi] using local_menu_product_bound X h86 label
    _ = _ := by simp [Fintype.card_fun]

end SymmetricSubgroupAsymptotics.MarkedC4.SolubleContainerCount
end
