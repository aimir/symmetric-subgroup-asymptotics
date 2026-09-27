import SymmetricSubgroupAsymptotics.RepeatedMarkerAllocationWeights
import SymmetricSubgroupAsymptotics.TernaryFullFactorSmall

/-!
# Exact empty and one-label marker multiplicity sums

These formulas concern the complete original positive-profile families.
The zero-size guard is retained: H(0,1)=0, whereas H(0,0)=1. A single
selected label with g>0 has exactly its literal multiplicity g, so its
weight is L3(g)/g!. No asymptotic or physical counting premise is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerProfileSmall

open FiniteLabelAllocations RepeatedMarkerAllocationWeights TernaryFullWeightReindex

@[simp] theorem markerProfileSum_zero_zero :
    markerProfileSum (Q := Fin 0) 0=1 := by
  let a : PositiveProfile (Q := Fin 0) 0 :=
    ⟨(fun i => Fin.elim0 i), (by intro i; exact Fin.elim0 i), (by simp)⟩
  have ha (b : PositiveProfile (Q := Fin 0) 0) : b=a := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i
  unfold markerProfileSum profileSum
  calc
    _ = ∏ q : Fin 0, (ternaryFullFactor (a.val q).val:ℚ) /
        (((a.val q).val).factorial:ℚ) := by
      apply Finset.sum_eq_single a
      · intro b _ hb
        exact False.elim (hb (ha b))
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    _ = 1 := by simp

theorem markerProfileSum_fin_zero_of_ne (g : ℕ) (hg : g ≠ 0) :
    markerProfileSum (Q := Fin 0) g=0 := by
  letI : IsEmpty (PositiveProfile (Q := Fin 0) g) := ⟨fun a => by
    apply hg
    simpa using a.property.2.symm⟩
  unfold markerProfileSum profileSum
  simp

/-- Empty selected-label set: the only nonzero profile is the empty one. -/
theorem markerProfileSum_fin_zero (g : ℕ) :
    markerProfileSum (Q := Fin 0) g=if g=0 then 1 else 0 := by
  by_cases hg : g=0
  · subst g
    simp
  · rw [if_neg hg,markerProfileSum_fin_zero_of_ne g hg]

private def oneProfile (g : ℕ) (hg : 0 < g) : PositiveProfile (Q := Fin 1) g :=
  ⟨(fun _ => ⟨g,Nat.lt_succ_self g⟩), (fun _ => hg), (by simp)⟩

private theorem oneProfile_unique (g : ℕ) (hg : 0 < g)
    (a : PositiveProfile (Q := Fin 1) g) : a=oneProfile g hg := by
  have hs : (a.val 0).val=g := by
    simpa only [Fin.sum_univ_one] using a.property.2
  apply Subtype.ext
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  apply Fin.ext
  exact hs

/-- A single selected character has its entire original g-coordinate fibre. -/
theorem markerProfileSum_fin_one_of_pos (g : ℕ) (hg : 0 < g) :
    markerProfileSum (Q := Fin 1) g=(ternaryFullFactor g:ℚ)/(g.factorial:ℚ) := by
  unfold markerProfileSum profileSum
  calc
    _ = ∏ q : Fin 1, (ternaryFullFactor ((oneProfile g hg).val q).val:ℚ) /
        ((((oneProfile g hg).val q).val).factorial:ℚ) := by
      apply Finset.sum_eq_single (oneProfile g hg)
      · intro a _ ha
        exact False.elim (ha (oneProfile_unique g hg a))
      · intro h
        exact False.elim (h (Finset.mem_univ _))
    _ = _ := by simp [oneProfile]

@[simp] theorem markerProfileSum_zero_one :
    markerProfileSum (Q := Fin 1) 0=0 := by
  letI : IsEmpty (PositiveProfile (Q := Fin 1) 0) := ⟨fun a => by
    have hp := a.property.1 0
    have hb := (a.val 0).isLt
    omega⟩
  unfold markerProfileSum profileSum
  simp

theorem markerProfileSum_fin_one (g : ℕ) :
    markerProfileSum (Q := Fin 1) g=
      if g=0 then 0 else (ternaryFullFactor g:ℚ)/(g.factorial:ℚ) := by
  by_cases hg : g=0
  · subst g
    simp
  · rw [if_neg hg,markerProfileSum_fin_one_of_pos g (Nat.pos_of_ne_zero hg)]

@[simp] theorem markerProfileSum_one_one :
    markerProfileSum (Q := Fin 1) 1=1 := by
  rw [markerProfileSum_fin_one_of_pos 1 (by decide)]
  simp [TernaryFullFactorSmall.factor_one]

end SymmetricSubgroupAsymptotics.RepeatedMarkerProfileSmall
