import SymmetricSubgroupAsymptotics.ChiefAbelianCompositionLength
import SymmetricSubgroupAsymptotics.NormalImageQuotient
import Mathlib.Algebra.BigOperators.Fin

/-!
# Abelian chief length above a unique nonabelian minimal normal subgroup

For the small nonsoluble affine complements, the published catalogue names
exhibit one nonabelian simple socle contained in every nontrivial normal
subgroup.  This file proves the series-independent consequence needed by the
fixed-target envelope: every abelian chief edge lies above that socle, so its
total charge is at most the total number of prime factors of the quotient.

The proof is entirely internal.  In particular, a catalogue row will only
have to identify the literal socle and its quotient order; it will not be
asked to state a bound on an arbitrarily chosen chief series.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical ArithmeticFunction.Omega IsMulCommutative

namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G]

/-- The total number of prime factors of the relative indices telescopes
along any monotone finite subgroup chain. -/
theorem subgroupSeries_cardFactors_sum :
    ∀ (n : ℕ) (f : Fin (n + 1) → Subgroup G), Monotone f →
      (∑ i : Fin n,
        ArithmeticFunction.cardFactors
          ((f i.castSucc).relIndex (f i.succ))) =
        ArithmeticFunction.cardFactors
          ((f 0).relIndex (f (Fin.last n))) := by
  intro n
  induction n with
  | zero =>
      intro f _
      simp
  | succ n ih =>
      intro f hf
      let g : Fin (n + 1) → Subgroup G := fun i => f i.castSucc
      have hg : Monotone g := fun _ _ h => hf h
      rw [Fin.sum_univ_castSucc]
      have hprefix := ih g hg
      have hle : f 0 ≤ f (Fin.last n).castSucc := hf (Fin.zero_le _)
      have hle' : f (Fin.last n).castSucc ≤ f (Fin.last (n + 1)) :=
        hf (Fin.le_last _)
      change (∑ i : Fin n,
          ArithmeticFunction.cardFactors
            ((f i.castSucc.castSucc).relIndex (f i.succ.castSucc))) =
          ArithmeticFunction.cardFactors
            ((f 0).relIndex (f (Fin.last n).castSucc)) at hprefix
      change (∑ i : Fin n,
          ArithmeticFunction.cardFactors
            ((f i.castSucc.castSucc).relIndex (f i.succ.castSucc))) +
          ArithmeticFunction.cardFactors
            ((f (Fin.last n).castSucc).relIndex (f (Fin.last (n + 1)))) = _
      rw [hprefix]
      exact (relativeIndex_cardFactors_add (f 0)
        (f (Fin.last n).castSucc) (f (Fin.last (n + 1))) hle hle').symm

/-- A chosen chief series charges no more abelian factors than occur in the
order of the whole group. -/
theorem actualChiefSeriesAbelianLength_le_cardFactors
    (s : ActualChiefSeries G) :
    actualChiefSeriesAbelianLength s ≤
      ArithmeticFunction.cardFactors (Nat.card G) := by
  have hs : Monotone s.subgroup :=
    (Fin.strictMono_iff_lt_succ.mpr s.step).monotone
  have hcard (i : Fin s.length) :
      Nat.card
          (normalChainQuotient
            (s.subgroup i.castSucc) (s.subgroup i.succ)) =
        (s.subgroup i.castSucc).relIndex (s.subgroup i.succ) := by
    have h := Subgroup.relIndex_ker (s.subgroup i.succ)
      (QuotientGroup.mk' (s.subgroup i.castSucc))
    simpa only [QuotientGroup.ker_mk', normalChainQuotient] using h.symm
  calc
    actualChiefSeriesAbelianLength s ≤
        ∑ i : Fin s.length,
          ArithmeticFunction.cardFactors
            ((s.subgroup i.castSucc).relIndex (s.subgroup i.succ)) := by
      apply Finset.sum_le_sum
      intro i _
      classical
      unfold chiefAbelianLength
      split
      · exact (congrArg ArithmeticFunction.cardFactors (hcard i)).le
      · exact Nat.zero_le _
    _ = ArithmeticFunction.cardFactors
          ((s.subgroup 0).relIndex (s.subgroup (Fin.last s.length))) :=
      subgroupSeries_cardFactors_sum s.length s.subgroup hs
    _ = ArithmeticFunction.cardFactors (Nat.card G) := by
      rw [s.head, s.last, Subgroup.relIndex_top_right, Subgroup.index_bot]

/-- If `E` is nonabelian and lies in every nontrivial normal subgroup, then
every abelian chief factor of `G` occurs above `E`. -/
theorem actualChiefSeriesAbelianLength_le_quotient_cardFactors
    (s : ActualChiefSeries G)
    (E : Subgroup G) [E.Normal]
    (hE : E ≠ ⊥)
    (hnc : ¬ IsMulCommutative E)
    (hcover : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → E ≤ N) :
    actualChiefSeriesAbelianLength s ≤
      ArithmeticFunction.cardFactors (Nat.card (G ⧸ E)) := by
  have hG : Nontrivial G := by
    letI : Nontrivial E := E.nontrivial_iff_ne_bot.mpr hE
    exact Function.Injective.nontrivial E.subtype_injective
  letI : Nontrivial G := hG
  have hlen : 0 < s.length := by
    by_contra h
    have hs0 : s.length = 0 := Nat.eq_zero_of_not_pos h
    have hbt : (⊥ : Subgroup G) = ⊤ := by
      calc
        (⊥ : Subgroup G) = s.subgroup 0 := s.head.symm
        _ = s.subgroup (Fin.last s.length) := by
          congr 1
          ext
          simp [hs0]
        _ = ⊤ := s.last
    exact not_subsingleton G
      (Subgroup.subsingleton_iff.mp (subsingleton_iff_bot_eq_top.mp hbt))
  let i0 : Fin s.length := ⟨0, hlen⟩
  have hfirst_ne : s.subgroup i0.succ ≠ ⊥ := by
    intro h
    have hstep := s.step i0
    have hbot : s.subgroup i0.castSucc = ⊥ := by
      have hi : i0.castSucc = (0 : Fin (s.length + 1)) := by ext; rfl
      rw [hi, s.head]
    rw [hbot, h] at hstep
    exact (lt_irrefl (⊥ : Subgroup G)) hstep
  have hEfirst : E = s.subgroup i0.succ := by
    have hle := hcover (s.subgroup i0.succ) (s.normal i0.succ) hfirst_ne
    have hbot : s.subgroup i0.castSucc = ⊥ := by
      have hi : i0.castSucc = (0 : Fin (s.length + 1)) := by ext; rfl
      rw [hi, s.head]
    rcases s.chief i0 E (inferInstance : E.Normal)
      (by rw [hbot]; exact bot_le) hle with h | h
    · exact absurd (h.trans hbot) hE
    · exact h
  have hfirst_zero :
      chiefAbelianLength
          (normalChainQuotient
            (s.subgroup i0.castSucc) (s.subgroup i0.succ)) = 0 := by
    have hbot : s.subgroup i0.castSucc = ⊥ := by
      have hi : i0.castSucc = (0 : Fin (s.length + 1)) := by ext; rfl
      rw [hi, s.head]
    let eTop : s.subgroup i0.succ ≃* E :=
      MulEquiv.subgroupCongr hEfirst.symm
    let π : s.subgroup i0.succ →* E := eTop.toMonoidHom
    have hπ : Function.Surjective π := eTop.surjective
    have hB : s.subgroup i0.castSucc =
        π.ker.map (s.subgroup i0.succ).subtype := by
      rw [hbot, π.ker_eq_bot_iff.mpr eTop.injective, Subgroup.map_bot]
    let e : normalChainQuotient
          (s.subgroup i0.castSucc) (s.subgroup i0.succ) ≃* E :=
      normalSectionQuotientEquiv (s.subgroup i0.succ)
        (s.subgroup i0.castSucc) π hπ hB
    rw [chiefAbelianLength_congr e]
    exact chiefAbelianLength_nonabelian E hnc
  have hs : Monotone s.subgroup :=
    (Fin.strictMono_iff_lt_succ.mpr s.step).monotone
  have hcard (i : Fin s.length) :
      Nat.card
          (normalChainQuotient
            (s.subgroup i.castSucc) (s.subgroup i.succ)) =
        (s.subgroup i.castSucc).relIndex (s.subgroup i.succ) := by
    have h := Subgroup.relIndex_ker (s.subgroup i.succ)
      (QuotientGroup.mk' (s.subgroup i.castSucc))
    simpa only [QuotientGroup.ker_mk', normalChainQuotient] using h.symm
  have hsum :
      actualChiefSeriesAbelianLength s +
          ArithmeticFunction.cardFactors
            ((s.subgroup i0.castSucc).relIndex (s.subgroup i0.succ)) ≤
        ∑ i : Fin s.length,
          ArithmeticFunction.cardFactors
            ((s.subgroup i.castSucc).relIndex (s.subgroup i.succ)) := by
    let firstFactor := ArithmeticFunction.cardFactors
      ((s.subgroup i0.castSucc).relIndex (s.subgroup i0.succ))
    have hpoint (i : Fin s.length) :
        chiefAbelianLength
              (normalChainQuotient
                (s.subgroup i.castSucc) (s.subgroup i.succ)) +
            (if i = i0 then firstFactor else 0) ≤
          ArithmeticFunction.cardFactors
            ((s.subgroup i.castSucc).relIndex (s.subgroup i.succ)) := by
      by_cases hi : i = i0
      · subst i
        simp only [hfirst_zero, zero_add, firstFactor, if_true]
        exact le_rfl
      · simp only [if_neg hi, add_zero]
        classical
        unfold chiefAbelianLength
        split
        · exact (congrArg ArithmeticFunction.cardFactors (hcard i)).le
        · exact Nat.zero_le _
    have hall := Finset.sum_le_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin s.length))) => hpoint i)
    rw [Finset.sum_add_distrib] at hall
    have hfirstSum :
        (∑ i : Fin s.length, if i = i0 then firstFactor else 0) =
          firstFactor := by simp
    simpa only [actualChiefSeriesAbelianLength, hfirstSum, firstFactor] using hall
  have htotal := subgroupSeries_cardFactors_sum s.length s.subgroup hs
  have hbot : s.subgroup i0.castSucc = ⊥ := by
    have hi : i0.castSucc = (0 : Fin (s.length + 1)) := by ext; rfl
    rw [hi, s.head]
  have hfactor :
      ArithmeticFunction.cardFactors (Nat.card G) =
        ArithmeticFunction.cardFactors (Nat.card E) +
          ArithmeticFunction.cardFactors (Nat.card (G ⧸ E)) := by
    rw [← E.card_mul_index, ArithmeticFunction.cardFactors_mul]
    · rw [E.index_eq_card]
    · exact Nat.ne_of_gt Nat.card_pos
    · exact Subgroup.index_ne_zero_of_finite
  have hfirstCard :
      ArithmeticFunction.cardFactors
          ((s.subgroup i0.castSucc).relIndex (s.subgroup i0.succ)) =
        ArithmeticFunction.cardFactors (Nat.card E) := by
    rw [hbot, ← hEfirst]
    simp [Subgroup.relIndex, Subgroup.index_bot]
  rw [htotal, s.head, s.last, Subgroup.relIndex_top_right,
    Subgroup.index_bot, hfirstCard, hfactor] at hsum
  omega

end SymmetricSubgroupAsymptotics

end
