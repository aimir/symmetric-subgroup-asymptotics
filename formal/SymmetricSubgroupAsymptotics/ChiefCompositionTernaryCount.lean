import SymmetricSubgroupAsymptotics.ChiefCompositionLength
import SymmetricSubgroupAsymptotics.SubnormalCompositionIndices
import Mathlib.Algebra.BigOperators.Fin

/-! A chosen actual chief series is bounded by the number of actual
order-three composition factors in any supplied composition series.
Abelian chief intervals charge precisely their order-three edges;
nonabelian chief factors have zero charge. The final change of series
uses the proved relative-index Jordan–Hölder theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics

variable {R : Type} [Group R] [Finite R]

private theorem subgroupSeries_valuation_le_potential :
    ∀ (n : ℕ) (f : Fin (n+1) → Subgroup R) (z : Fin (n+1) → ℕ),
      Monotone f →
      (∀ i : Fin n, ((f i.castSucc).relIndex (f i.succ)).factorization 3 +
        z i.castSucc ≤ z i.succ) →
      ((f 0).relIndex (f (Fin.last n))).factorization 3 + z 0 ≤ z (Fin.last n) := by
  intro n
  induction n with
  | zero => intro f z _ _; simp
  | succ n ih =>
    intro f z hf he
    let g : Fin (n+1) → Subgroup R := fun i => f i.castSucc
    let y : Fin (n+1) → ℕ := fun i => z i.castSucc
    have hp := ih g y (fun i j h => hf h) (fun i => he i.castSucc)
    have hl := he (Fin.last n)
    have hv := relativeIndex_ternary_add (f 0) (f (Fin.last n).castSucc)
      (f (Fin.last (n+1))) (hf (Fin.zero_le _)) (hf (Fin.le_last _))
    change ((f 0).relIndex (f (Fin.last n).castSucc)).factorization 3 +
      z 0 ≤ z (Fin.last n).castSucc at hp
    change ((f (Fin.last n).castSucc).relIndex (f (Fin.last (n+1)))).factorization 3 +
      z (Fin.last n).castSucc ≤ z (Fin.last (n+1)) at hl
    omega

def compositionTernaryEdge (t : SubnormalCompositionSeries R) (i : Fin t.chain.length) : ℕ :=
  if (t.chain i.castSucc).val.relIndex (t.chain i.succ).val = 3 then 1 else 0

def compositionTernaryPrefix (t : SubnormalCompositionSeries R) :
    Fin (t.chain.length+1) → ℕ := Fin.partialSum (compositionTernaryEdge t)

omit [Finite R] in
theorem compositionTernaryPrefix_mono (t : SubnormalCompositionSeries R) :
    Monotone (compositionTernaryPrefix t) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  change Fin.partialSum (compositionTernaryEdge t) i.castSucc ≤
    Fin.partialSum (compositionTernaryEdge t) i.succ
  rw [Fin.partialSum_succ]
  exact Nat.le_add_right _ _

omit [Finite R] in
@[simp] theorem compositionTernaryPrefix_zero (t : SubnormalCompositionSeries R) :
    compositionTernaryPrefix t 0 = 0 := Fin.partialSum_zero _

omit [Finite R] in
theorem compositionTernaryPrefix_last (t : SubnormalCompositionSeries R) :
    compositionTernaryPrefix t (Fin.last t.chain.length) = compositionOrderCount 3 t := by
  change ((List.ofFn (compositionTernaryEdge t)).take t.chain.length).sum = _
  have hlen : (List.ofFn (compositionTernaryEdge t)).length = t.chain.length := List.length_ofFn
  have ht : (List.ofFn (compositionTernaryEdge t)).take t.chain.length =
      List.ofFn (compositionTernaryEdge t) := by
    have ht' : (List.ofFn (compositionTernaryEdge t)).take
        (List.ofFn (compositionTernaryEdge t)).length = List.ofFn (compositionTernaryEdge t) :=
      List.take_length
    simpa only [hlen] using ht'
  rw [ht, List.sum_ofFn]
  rfl

/-- An abelian chief interval spends only the order-three factors in
its actual composition refinement, not every composition edge. -/
theorem compositionSeries_abelian_interval_ternary_count
    (t : SubnormalCompositionSeries R) (i j : Fin (t.chain.length+1)) (hij : i ≤ j)
    (B L : Subgroup R) [B.Normal] [L.Normal]
    [IsMulCommutative (normalChainQuotient B L)]
    (hB : (t.chain i).val = B) (hL : (t.chain j).val = L) :
    (Nat.card (normalChainQuotient B L)).factorization 3 + compositionTernaryPrefix t i ≤
      compositionTernaryPrefix t j := by
  let d := j.val-i.val
  let e (k : Fin (d+1)) : Fin (t.chain.length+1) := ⟨i.val+k.val, by
    have hk := k.2
    have hj := j.2
    have hi : i.val ≤ j.val := hij
    dsimp [d] at hk
    omega⟩
  let f (k : Fin (d+1)) : Subgroup R := (t.chain (e k)).val
  let z (k : Fin (d+1)) : ℕ := compositionTernaryPrefix t (e k)
  have ht := (compositionSeries_strictMono t).monotone
  have hf : Monotone f := by
    intro k l hkl
    apply ht
    change i.val+k.val ≤ i.val+l.val
    omega
  have he (k : Fin d) : ((f k.castSucc).relIndex (f k.succ)).factorization 3 +
      z k.castSucc ≤ z k.succ := by
    let q : Fin t.chain.length := ⟨i.val+k.val, by
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
      change i.val ≤ i.val+k.val
      omega
    have hhi : (t.chain q.succ).val ≤ L := by
      rw [← hL]
      apply ht
      have hk := k.2
      have hi : i.val ≤ j.val := hij
      change i.val+k.val+1 ≤ j.val
      dsimp [d] at hk
      omega
    letI := abelianInterval_quotient_commutative B L
      (t.chain q.castSucc).val (t.chain q.succ).val hlo (t.chain.step q).le hhi
    have hp : ((t.chain q.castSucc).val.relIndex (t.chain q.succ).val).Prime := by
      simpa only [Subgroup.relIndex, Subgroup.index_eq_card] using
        (IsSimpleGroup.prime_card (α := (t.chain q.succ).val ⧸
          (t.chain q.castSucc).val.subgroupOf (t.chain q.succ).val))
    change ((t.chain q.castSucc).val.relIndex (t.chain q.succ).val).factorization 3 +
      Fin.partialSum (compositionTernaryEdge t) q.castSucc ≤
      Fin.partialSum (compositionTernaryEdge t) q.succ
    rw [Fin.partialSum_succ, hp.factorization]
    simp only [Finsupp.single_apply, compositionTernaryEdge]
    omega
  have h := subgroupSeries_valuation_le_potential d f z hf he
  have he0 : e 0 = i := Fin.ext (Nat.add_zero _)
  have hel : e (Fin.last d) = j := by
    apply Fin.ext
    change i.val+(j.val-i.val)=j.val
    omega
  have h0 : f 0 = B := by simpa only [f, he0] using hB
  have hl : f (Fin.last d) = L := by simpa only [f, hel] using hL
  rw [h0, hl, ← normalChainQuotient_card B L] at h
  simpa only [z, he0, hel] using h

theorem actualChiefWeight_le_refinement_ternary_count (s : ActualChiefSeries R)
    (t : SubnormalCompositionSeries R)
    (j : Fin (s.length+1) ↪ Fin (t.chain.length+1))
    (he : ∀ i, (t.chain (j i)).val = s.subgroup i)
    (h0 : j 0 = 0) (hl : j (Fin.last s.length) = Fin.last t.chain.length) :
    actualChiefSeriesTernaryWeight s ≤ compositionOrderCount 3 t := by
  classical
  have hj : StrictMono j := by
    intro a b hab
    apply (compositionSeries_strictMono t).lt_iff_lt.mp
    rw [he, he]
    exact actualChiefSeries_strictMono s hab
  let z (i : Fin (s.length+1)) : ℕ := compositionTernaryPrefix t (j i)
  have hi (i : Fin s.length) :
      chiefTernaryWeight (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ)) +
        z i.castSucc ≤ z i.succ := by
    by_cases hab : IsMulCommutative
      (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
    · letI := hab
      rw [chiefTernaryWeight, if_pos hab]
      exact compositionSeries_abelian_interval_ternary_count t (j i.castSucc) (j i.succ)
        (hj.monotone (Fin.castSucc_le_succ i)) _ _ (he _) (he _)
    · rw [chiefTernaryWeight_nonabelian _ hab, zero_add]
      exact compositionTernaryPrefix_mono t (hj.monotone (Fin.castSucc_le_succ i))
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin s.length))) => hi i)
  rw [Finset.sum_add_distrib] at hsum
  have htel : z 0 + (∑ i : Fin s.length, z i.succ) =
      (∑ i : Fin s.length, z i.castSucc) + z (Fin.last s.length) :=
    (Fin.sum_univ_succ z).symm.trans (Fin.sum_univ_castSucc z)
  have hz0 : z 0 = 0 := by simp only [z, h0, compositionTernaryPrefix_zero]
  have hzl : z (Fin.last s.length) = compositionOrderCount 3 t := by
    simp only [z, hl, compositionTernaryPrefix_last]
  change actualChiefSeriesTernaryWeight s + _ ≤ _ at hsum
  omega

/-- Any supplied actual composition series bounds every chosen actual
chief series. The order-three count is transported by the proved index
Jordan–Hölder theorem, with no multiplicity-invariance hypothesis. -/
theorem actualChiefWeight_le_composition_ternary_count (s : ActualChiefSeries R)
    (t : SubnormalCompositionSeries R) :
    actualChiefSeriesTernaryWeight s ≤ compositionOrderCount 3 t := by
  obtain ⟨u, j, he, h0, hl⟩ := actualChiefSeries_composition_refinement s
  exact (actualChiefWeight_le_refinement_ternary_count s u j he h0 hl).trans_eq
    (compositionOrderCount_eq 3 u t)

theorem exists_actualChiefSeries_le_composition_ternary_count
    (t : SubnormalCompositionSeries R) :
    ∃ s : ActualChiefSeries R, actualChiefSeriesTernaryWeight s ≤ compositionOrderCount 3 t :=
  ⟨actualChiefSeries R, actualChiefWeight_le_composition_ternary_count (actualChiefSeries R) t⟩

end SymmetricSubgroupAsymptotics
