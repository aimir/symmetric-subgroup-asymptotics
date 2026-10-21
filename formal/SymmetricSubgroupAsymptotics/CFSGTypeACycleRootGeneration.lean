import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-! All scalar roots on one actual directed coordinate cycle generate
SL. Paths are handled uniformly by powers of that original permutation,
not by a finite-dimensional list of cases. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTypeACycleRootGeneration
open CFSGTypeAElementaryMatrices
variable {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F]

/-- A directed spanning cycle of full root groups generates the literal
special linear group over any field, in every dimension at least two. -/
theorem eq_top_of_cycle_roots (hn : 2≤Fintype.card n)
    (σ : Equiv.Perm n) (hσ : σ.IsCycleOn (Finset.univ : Finset n))
    (H : Subgroup (SL (n:=n) (F:=F)))
    (hEdge : ∀ i : n,∀ (hi : i≠σ i) (a : F),elementary hi a∈H) : H=⊤ := by
  have hnear : ∀ (i : n) (k : ℕ),0<k→k<Fintype.card n→i≠(σ^k) i := by
    intro i k hk hkn he
    have hd := (hσ.pow_apply_eq (Finset.mem_univ i)).mp he.symm
    rw [Finset.card_univ] at hd
    exact Nat.not_dvd_of_pos_of_lt hk hkn hd
  have hmove : ∀ i : n,i≠σ i := by
    intro i
    simpa only [pow_one] using hnear i 1 (by decide) (by omega)
  have hcomm : ∀ x y : SL (n:=n) (F:=F),x∈H→y∈H→⁅x,y⁆∈H := by
    intro x y hx hy
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)) (H.inv_mem hy)
  have hPath : ∀ (k : ℕ) (i : n) (hk : 0<k) (hkn : k<Fintype.card n) (a : F),
      elementary (hnear i k hk hkn) a∈H := by
    intro k
    induction k with
    | zero => intro i hk;omega
    | succ k ih =>
      intro i hk hkn a
      by_cases hk0 : k=0
      · subst k
        simpa only [zero_add,pow_one] using hEdge i (hmove i) a
      have hkpos : 0<k := Nat.pos_of_ne_zero hk0
      have hklt : k<Fintype.card n := by omega
      let j := (σ^k) i
      have hij : i≠j := hnear i k hkpos hklt
      have hjk : j≠σ j := hmove j
      have he : (σ^(k+1)) i=σ j := by simp only [pow_succ',Equiv.Perm.mul_apply,j]
      have hik : i≠σ j := he ▸ hnear i (k+1) hk hkn
      have hc := hcomm (elementary hij a) (elementary hjk (1 : F))
        (ih i hkpos hklt a) (hEdge j hjk 1)
      rw [elementary_commutator hij hjk hik,mul_one] at hc
      simpa only [he] using hc
  apply CFSGTypeAElementaryGeneration.eq_top_of_elementary H
  intro i j hij a
  obtain ⟨k,hkn,hk⟩ := hσ.exists_pow_eq (Finset.mem_univ i) (Finset.mem_univ j)
  rw [Finset.card_univ] at hkn
  have hkpos : 0<k := by
    by_contra h
    have hz : k=0 := by omega
    rw [hz,pow_zero,Equiv.Perm.one_apply] at hk
    exact hij hk
  have hp := hPath k i hkpos hkn a
  simpa only [hk] using hp

end SymmetricSubgroupAsymptotics.CFSGTypeACycleRootGeneration
