import SymmetricSubgroupAsymptotics.ChiefCompositionLength
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Abelian chief length versus actual composition length

An abelian chief factor of order `p^d` contributes `d` elementary
composition factors. Nonabelian chief factors contribute zero. This file
proves, on literal subgroup chains, that the resulting abelian chief length
is bounded by the length of every actual composition refinement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical ArithmeticFunction.Omega IsMulCommutative

namespace SymmetricSubgroupAsymptotics

def chiefAbelianLength (Q : Type) [Group Q] : ℕ := by
  classical
  exact if IsMulCommutative Q then ArithmeticFunction.cardFactors (Nat.card Q) else 0

theorem chiefAbelianLength_nonabelian (Q : Type) [Group Q]
    (hn : ¬ IsMulCommutative Q) : chiefAbelianLength Q = 0 := by
  simp [chiefAbelianLength, hn]

theorem chiefAbelianLength_congr
    {G Q : Type} [Group G] [Group Q] (e : G ≃* Q) :
    chiefAbelianLength G = chiefAbelianLength Q := by
  have hc : IsMulCommutative G ↔ IsMulCommutative Q := by
    constructor
    · intro h
      letI := h
      exact ⟨⟨fun x y => e.symm.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
    · intro h
      letI := h
      exact ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩
  classical
  by_cases h : IsMulCommutative G
  · have hq := hc.mp h
    simp [chiefAbelianLength, h, hq, Nat.card_congr e.toEquiv]
  · have hq : ¬ IsMulCommutative Q := fun hq => h (hc.mpr hq)
    simp [chiefAbelianLength, h, hq]

theorem chiefAbelianLength_elementary
    {Q V : Type} [Group Q] [AddCommGroup V]
    {p : ℕ} [hp : Fact p.Prime]
    [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
    (e : Q ≃* Multiplicative V) :
    chiefAbelianLength Q = Module.finrank (ZMod p) V := by
  have hcom : IsMulCommutative Q := ⟨⟨fun x y => e.injective (by
    rw [map_mul, map_mul, mul_comm])⟩⟩
  have he : Nat.card Q = Nat.card V := Nat.card_congr e.toEquiv
  rw [chiefAbelianLength, if_pos hcom, he,
    Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
    ArithmeticFunction.cardFactors_apply_prime_pow hp.out]

variable {R : Type} [Group R] [Finite R]

theorem relativeIndex_cardFactors_add
    (B C D : Subgroup R) (hBC : B ≤ C) (hCD : C ≤ D) :
    ArithmeticFunction.cardFactors (B.relIndex D) =
      ArithmeticFunction.cardFactors (B.relIndex C) +
        ArithmeticFunction.cardFactors (C.relIndex D) := by
  rw [← Subgroup.relIndex_mul_relIndex B C D hBC hCD,
    ArithmeticFunction.cardFactors_mul
      (show B.relIndex C ≠ 0 from Subgroup.index_ne_zero_of_finite)
      (show C.relIndex D ≠ 0 from Subgroup.index_ne_zero_of_finite)]

theorem subgroupSeries_cardFactors_le_length :
    ∀ (n : ℕ) (f : Fin (n + 1) → Subgroup R), Monotone f →
      (∀ i : Fin n,
        ArithmeticFunction.cardFactors
          ((f i.castSucc).relIndex (f i.succ)) ≤ 1) →
      ArithmeticFunction.cardFactors
        ((f 0).relIndex (f (Fin.last n))) ≤ n := by
  intro n
  induction n with
  | zero =>
      intro f _ _
      simp
  | succ n ih =>
      intro f hf he
      let g : Fin (n + 1) → Subgroup R := fun i => f i.castSucc
      have hprefix := ih g (fun i j h => hf h) (fun i => he i.castSucc)
      have hlast := he (Fin.last n)
      have hle : f 0 ≤ f (Fin.last n).castSucc := hf (Fin.zero_le _)
      have hle' : f (Fin.last n).castSucc ≤ f (Fin.last (n + 1)) :=
        hf (Fin.le_last _)
      have h := relativeIndex_cardFactors_add (f 0)
        (f (Fin.last n).castSucc) (f (Fin.last (n + 1))) hle hle'
      change ArithmeticFunction.cardFactors
        ((f 0).relIndex (f (Fin.last n).castSucc)) ≤ n at hprefix
      change ArithmeticFunction.cardFactors
        ((f (Fin.last n).castSucc).relIndex (f (Fin.last (n + 1)))) ≤ 1 at hlast
      omega

theorem compositionSeries_abelian_interval_cardFactors
    (t : SubnormalCompositionSeries R)
    (i j : Fin (t.chain.length + 1)) (hij : i ≤ j)
    (B L : Subgroup R) [B.Normal] [L.Normal]
    [IsMulCommutative (normalChainQuotient B L)]
    (hB : (t.chain i).val = B) (hL : (t.chain j).val = L) :
    ArithmeticFunction.cardFactors
      (Nat.card (normalChainQuotient B L)) ≤ j.val - i.val := by
  let d := j.val - i.val
  let e (k : Fin (d + 1)) : Fin (t.chain.length + 1) := ⟨i.val + k.val, by
    have hk := k.2
    have hj := j.2
    have hi : i.val ≤ j.val := hij
    dsimp [d] at hk
    omega⟩
  let f (k : Fin (d + 1)) : Subgroup R := (t.chain (e k)).val
  have ht := (compositionSeries_strictMono t).monotone
  have hf : Monotone f := by
    intro k l hkl
    apply ht
    change i.val + k.val ≤ i.val + l.val
    omega
  have hedge (k : Fin d) :
      ArithmeticFunction.cardFactors
        ((f k.castSucc).relIndex (f k.succ)) ≤ 1 := by
    let q : Fin t.chain.length := ⟨i.val + k.val, by
      have hk := k.2
      have hj := j.2
      have hi : i.val ≤ j.val := hij
      dsimp [d] at hk
      omega⟩
    obtain ⟨hn, hs⟩ := subnormalCover_quotient_simple
      (t.chain q.castSucc) (t.chain q.succ) (t.chain.step q)
    letI := hn
    letI := hs
    have hlo : B ≤ (t.chain q.castSucc).val := by
      rw [← hB]
      apply ht
      change i.val ≤ i.val + k.val
      omega
    have hhi : (t.chain q.succ).val ≤ L := by
      rw [← hL]
      apply ht
      have hk := k.2
      have hi : i.val ≤ j.val := hij
      change i.val + k.val + 1 ≤ j.val
      dsimp [d] at hk
      omega
    letI := abelianInterval_quotient_commutative B L
      (t.chain q.castSucc).val (t.chain q.succ).val hlo
        (t.chain.step q).le hhi
    have hp : ((t.chain q.castSucc).val.relIndex
        (t.chain q.succ).val).Prime := by
      simpa only [Subgroup.relIndex, Subgroup.index_eq_card] using
        (IsSimpleGroup.prime_card
          (α := (t.chain q.succ).val ⧸
            (t.chain q.castSucc).val.subgroupOf (t.chain q.succ).val))
    simpa only [f, e, q] using
      (ArithmeticFunction.cardFactors_apply_prime hp).le
  have h := subgroupSeries_cardFactors_le_length d f hf hedge
  have he0 : e 0 = i := Fin.ext (Nat.add_zero _)
  have hel : e (Fin.last d) = j := by
    apply Fin.ext
    change i.val + (j.val - i.val) = j.val
    omega
  have h0 : f 0 = B := by simpa only [f, he0] using hB
  have hl : f (Fin.last d) = L := by simpa only [f, hel] using hL
  rw [h0, hl, ← normalChainQuotient_card B L] at h
  simpa only [d] using h

def actualChiefSeriesAbelianLength (s : ActualChiefSeries R) : ℕ :=
  ∑ i : Fin s.length, chiefAbelianLength
    (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))

theorem actualChiefAbelianLength_le_compositionLength
    (s : ActualChiefSeries R) (t : SubnormalCompositionSeries R)
    (j : Fin (s.length + 1) ↪ Fin (t.chain.length + 1))
    (he : ∀ i, (t.chain (j i)).val = s.subgroup i)
    (h0 : j 0 = 0)
    (hl : j (Fin.last s.length) = Fin.last t.chain.length) :
    actualChiefSeriesAbelianLength s ≤ t.chain.length := by
  classical
  have hj : StrictMono j := by
    intro a b hab
    apply (compositionSeries_strictMono t).lt_iff_lt.mp
    rw [he, he]
    exact actualChiefSeries_strictMono s hab
  let z (i : Fin (s.length + 1)) : ℕ := (j i).val
  have hi (i : Fin s.length) :
      chiefAbelianLength
          (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ)) ≤
        z i.succ - z i.castSucc := by
    by_cases hab : IsMulCommutative
        (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
    · letI := hab
      rw [chiefAbelianLength, if_pos hab]
      exact compositionSeries_abelian_interval_cardFactors t
        (j i.castSucc) (j i.succ)
        (hj.monotone (Fin.castSucc_le_succ i)) _ _ (he _) (he _)
    · rw [chiefAbelianLength_nonabelian _ hab]
      exact Nat.zero_le _
  have hz (i : Fin s.length) :
      (z i.succ - z i.castSucc) + z i.castSucc = z i.succ :=
    Nat.sub_add_cancel (hj.monotone (Fin.castSucc_le_succ i))
  have hsum :
      (∑ i : Fin s.length, (z i.succ - z i.castSucc)) +
          (∑ i : Fin s.length, z i.castSucc) =
        ∑ i : Fin s.length, z i.succ := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => hz i)
  have htel : z 0 + (∑ i : Fin s.length, z i.succ) =
      (∑ i : Fin s.length, z i.castSucc) + z (Fin.last s.length) :=
    (Fin.sum_univ_succ z).symm.trans (Fin.sum_univ_castSucc z)
  have hz0 : z 0 = 0 := congrArg Fin.val h0
  have hzl : z (Fin.last s.length) = t.chain.length := congrArg Fin.val hl
  have hgap : (∑ i : Fin s.length, (z i.succ - z i.castSucc)) =
      t.chain.length := by omega
  calc
    actualChiefSeriesAbelianLength s ≤
        ∑ i : Fin s.length, (z i.succ - z i.castSucc) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = t.chain.length := hgap

theorem actualChiefAbelianLength_le_some_compositionLength
    (s : ActualChiefSeries R) :
    ∃ t : SubnormalCompositionSeries R,
      actualChiefSeriesAbelianLength s ≤ t.chain.length := by
  obtain ⟨t, j, he, h0, hl⟩ := actualChiefSeries_composition_refinement s
  exact ⟨t, actualChiefAbelianLength_le_compositionLength s t j he h0 hl⟩

end SymmetricSubgroupAsymptotics

end
