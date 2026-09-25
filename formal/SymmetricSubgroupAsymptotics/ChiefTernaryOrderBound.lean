import SymmetricSubgroupAsymptotics.SubgroupSeriesValuation
import Mathlib.Algebra.BigOperators.Fin

/-! A safe order bound for the weight of an actual chosen chief series.
The order valuation is only an upper bound: nonabelian factors still have
zero chief weight, including when their order is divisible by three. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {R:Type} [Group R] [Finite R]

/-- Relative-index valuations telescope along the literal subgroup chain. -/
theorem subgroupSeries_ternary_valuation_sum :
    ∀ (n:ℕ) (f:Fin (n+1)→Subgroup R),Monotone f →
      (∑i:Fin n,((f i.castSucc).relIndex (f i.succ)).factorization 3)=
        ((f 0).relIndex (f (Fin.last n))).factorization 3 := by
  intro n
  induction n with
  | zero =>
    intro f _
    simp
  | succ n ih =>
    intro f hf
    let g : Fin (n+1)→Subgroup R := fun i=>f i.castSucc
    have hg : Monotone g := fun i j h=>hf h
    rw [Fin.sum_univ_castSucc]
    have hprefix := ih g hg
    have hle : f 0≤f (Fin.last n).castSucc := hf (Fin.zero_le _)
    have hle' : f (Fin.last n).castSucc≤f (Fin.last (n+1)) := hf (Fin.le_last _)
    change (∑i:Fin n,((f i.castSucc.castSucc).relIndex
      (f i.succ.castSucc)).factorization 3)=
        ((f 0).relIndex (f (Fin.last n).castSucc)).factorization 3 at hprefix
    change (∑i:Fin n,((f i.castSucc.castSucc).relIndex
      (f i.succ.castSucc)).factorization 3)+
        ((f (Fin.last n).castSucc).relIndex (f (Fin.last (n+1)))).factorization 3=_
    rw [hprefix]
    exact (relativeIndex_ternary_add (f 0) (f (Fin.last n).castSucc)
      (f (Fin.last (n+1))) hle hle').symm

/-- An actual chosen chief weight never exceeds the ternary valuation
of the original group order. This does not identify that valuation with
the number of order-three composition factors. -/
theorem actualChiefSeriesTernaryWeight_le_order (s:ActualChiefSeries R) :
    actualChiefSeriesTernaryWeight s≤(Nat.card R).factorization 3 := by
  have hs : Monotone s.subgroup :=
    (Fin.strictMono_iff_lt_succ.mpr s.step).monotone
  have hcard (i:Fin s.length) :
      Nat.card (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))=
        (s.subgroup i.castSucc).relIndex (s.subgroup i.succ) := by
    have h := Subgroup.relIndex_ker (s.subgroup i.succ)
      (QuotientGroup.mk' (s.subgroup i.castSucc))
    simpa only [QuotientGroup.ker_mk',normalChainQuotient] using h.symm
  calc
    actualChiefSeriesTernaryWeight s≤
        ∑i:Fin s.length,((s.subgroup i.castSucc).relIndex
          (s.subgroup i.succ)).factorization 3 := by
      apply Finset.sum_le_sum
      intro i _
      classical
      dsimp only [chiefTernaryWeight]
      split
      · exact (congrArg (fun n:ℕ=>n.factorization 3) (hcard i)).le
      · exact Nat.zero_le _
    _=((s.subgroup 0).relIndex (s.subgroup (Fin.last s.length))).factorization 3 :=
      subgroupSeries_ternary_valuation_sum s.length s.subgroup hs
    _=(Nat.card R).factorization 3 := by
      rw [s.head,s.last,Subgroup.relIndex_top_right,Subgroup.index_bot]

end SymmetricSubgroupAsymptotics
