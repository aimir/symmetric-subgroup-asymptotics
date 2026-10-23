import SymmetricSubgroupAsymptotics.LinearCentralizerTripleEvaluation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-! An invertible operator over a two-element field either has three
independent successive orbit vectors, is an involution, or satisfies
T^2+T+I=0. The proof uses a union of TWO subspaces, not a minimal
polynomial or a rational canonical form. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryLinearQuadraticDichotomy

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem scalar_eq_zero_or_one (hK : Nat.card K=2) (c : K) : c=0 ∨ c=1 := by
  by_cases hc : c=0
  · exact Or.inl hc
  obtain ⟨a, ha, huniq⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  exact Or.inr ((huniq c hc).trans (huniq 1 one_ne_zero).symm)

theorem neg_eq_self (hK : Nat.card K=2) (v : V) : -v=v := by
  have hneg : (-1 : K)=1 :=
    (scalar_eq_zero_or_one hK (-1)).resolve_left (neg_ne_zero.mpr one_ne_zero)
  rw [←neg_one_smul K v, hneg, one_smul]

theorem submodule_eq_top_or_eq_top_of_cover (A B : Submodule K V)
    (h : ∀v : V, v ∈ A ∨ v ∈ B) : A=⊤ ∨ B=⊤ := by
  by_cases hA : A=⊤
  · exact Or.inl hA
  right
  obtain ⟨x, hx⟩ : ∃x : V, x ∉ A := by
    by_contra hn
    exact hA (Submodule.eq_top_iff'.mpr (by simpa only [not_exists, not_not] using hn))
  have hxB : x ∈ B := (h x).resolve_left hx
  apply Submodule.eq_top_iff'.mpr
  intro y
  rcases h y with hy | hy
  · have hxy : x+y ∉ A := by
      intro hxy
      exact hx (by simpa using A.sub_mem hxy hy)
    have hxyB := (h (x+y)).resolve_left hxy
    simpa using B.sub_mem hxyB hxB
  · exact hy

theorem pointwise_quadratic (hK : Nat.card K=2)
    (e : V ≃ₗ[K] V) (v : V)
    (hv : ¬ LinearIndependent K ![v,e v,e (e v)]) :
    e (e v)=v ∨ e (e v)+e v+v=0 := by
  obtain ⟨g, hrel, hn⟩ := Fintype.not_linearIndependent_iff.mp hv
  have hrel' : g 0 • v + g 1 • e v + g 2 • e (e v)=0 := by
    simpa only [Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two] using hrel
  have hnon : g 0 ≠ 0 ∨ g 1 ≠ 0 ∨ g 2 ≠ 0 := by
    obtain ⟨i, hi⟩ := hn
    fin_cases i <;> simp_all
  have hdouble (x : V) : x+x=0 := by
    calc
      x+x = -x+x := congrArg (fun y : V => y+x) (neg_eq_self hK x).symm
      _ = 0 := neg_add_cancel x
  have hadd (x y : V) (h : x+y=0) : y=x :=
    add_left_cancel (h.trans (hdouble x).symm)
  rcases scalar_eq_zero_or_one hK (g 0) with h0 | h0 <;>
    rcases scalar_eq_zero_or_one hK (g 1) with h1 | h1 <;>
    rcases scalar_eq_zero_or_one hK (g 2) with h2 | h2
  all_goals simp only [h0, h1, h2, zero_smul, one_smul, zero_add, add_zero] at hrel'
  · exact False.elim (by simpa only [h0, h1, h2, ne_eq, not_true_eq_false,
      or_self] using hnon)
  · have he0 : e v=0 := e.injective (hrel'.trans (map_zero e).symm)
    have hv0 : v=0 := e.injective (he0.trans (map_zero e).symm)
    exact Or.inl (by simp only [hv0, map_zero])
  · have hv0 : v=0 := e.injective (hrel'.trans (map_zero e).symm)
    exact Or.inl (by simp only [hv0, map_zero])
  · have heq : e (e v)=e v := hadd _ _ hrel'
    exact Or.inl (heq.trans (e.injective heq))
  · exact Or.inl (by simp only [hrel', map_zero])
  · exact Or.inl (hadd _ _ hrel')
  · have heq : e v=v := hadd _ _ hrel'
    exact Or.inl ((congrArg e heq).trans heq)
  · right
    calc
      e (e v)+e v+v = v+e v+e (e v) := by abel
      _ = 0 := hrel'

theorem independent_triple_or_quadratic (hK : Nat.card K=2) (e : V ≃ₗ[K] V) :
    (∃v : V, LinearIndependent K ![v,e v,e (e v)]) ∨
      (∀v : V, e (e v)=v) ∨ (∀v : V, e (e v)+e v+v=0) := by
  by_cases h : ∃v : V, LinearIndependent K ![v,e v,e (e v)]
  · exact Or.inl h
  right
  let A : Submodule K V := (e.toLinearMap.comp e.toLinearMap-LinearMap.id).ker
  let B : Submodule K V :=
    (e.toLinearMap.comp e.toLinearMap+e.toLinearMap+LinearMap.id).ker
  have hcover : ∀v : V, v ∈ A ∨ v ∈ B := by
    intro v
    rcases pointwise_quadratic hK e v (fun hv => h ⟨v, hv⟩) with hv | hv
    · exact Or.inl (show e (e v)-v=0 from sub_eq_zero.mpr hv)
    · exact Or.inr hv
  rcases submodule_eq_top_or_eq_top_of_cover A B hcover with hA | hB
  · left
    intro v
    have hv : v ∈ A := by rw [hA]; trivial
    exact sub_eq_zero.mp (show e (e v)-v=0 from hv)
  · right
    intro v
    have hv : v ∈ B := by rw [hB]; trivial
    exact hv

end SymmetricSubgroupAsymptotics.BinaryLinearQuadraticDichotomy
