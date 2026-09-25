import SymmetricSubgroupAsymptotics.AbelianCompositionWeights
import SymmetricSubgroupAsymptotics.SubgroupSeriesValuation

/-! An actual chief chain's ternary weight is bounded by the length of
an actual composition refinement. This comparison needs no invariance
of abstract composition multiplicities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {R:Type} [Group R] [Finite R]

theorem actualChiefSeries_strictMono (s:ActualChiefSeries R) : StrictMono s.subgroup :=
  Fin.strictMono_iff_lt_succ.mpr s.step

theorem compositionSeries_strictMono (t:SubnormalCompositionSeries R) :
    StrictMono (fun i=>(t.chain i).val) :=
  Fin.strictMono_iff_lt_succ.mpr (fun i=>(t.chain.step i).1)

theorem normalChainQuotient_card (B L:Subgroup R) [B.Normal] [L.Normal] :
    Nat.card (normalChainQuotient B L)=B.relIndex L := by
  have h := Subgroup.relIndex_ker L (QuotientGroup.mk' B)
  simpa only [QuotientGroup.ker_mk',normalChainQuotient] using h.symm

/-- Within an actual abelian chief interval, the ternary factor weight
is at most the number of genuine refined composition edges. -/
theorem compositionSeries_abelian_interval (t:SubnormalCompositionSeries R)
    (i j:Fin (t.chain.length+1)) (hij:i ≤ j)
    (B L:Subgroup R) [B.Normal] [L.Normal]
    [IsMulCommutative (normalChainQuotient B L)]
    (hB:(t.chain i).val=B) (hL:(t.chain j).val=L) :
    (Nat.card (normalChainQuotient B L)).factorization 3 ≤ j.val-i.val := by
  let d := j.val-i.val
  let e (k:Fin (d+1)) : Fin (t.chain.length+1) := ⟨i.val+k.val,by
    have hk := k.2
    have hj := j.2
    have hi : i.val ≤ j.val := hij
    dsimp [d] at hk
    omega⟩
  let f (k:Fin (d+1)) : Subgroup R := (t.chain (e k)).val
  have ht := (compositionSeries_strictMono t).monotone
  have hf : Monotone f := by
    intro k l hkl
    apply ht
    change i.val+k.val ≤ i.val+l.val
    omega
  have he (k:Fin d) : ((f k.castSucc).relIndex (f k.succ)).factorization 3 ≤ 1 := by
    let q : Fin t.chain.length := ⟨i.val+k.val,by
      have hk := k.2
      have hj := j.2
      have hi : i.val ≤ j.val := hij
      dsimp [d] at hk
      omega⟩
    obtain ⟨hn,hs⟩ := subnormalCover_quotient_simple
      (t.chain q.castSucc) (t.chain q.succ) (t.chain.step q)
    letI := hn
    letI := hs
    have hlo : B ≤ (t.chain q.castSucc).val := by
      rw [←hB]
      apply ht
      change i.val ≤ i.val+k.val
      omega
    have hhi : (t.chain q.succ).val ≤ L := by
      rw [←hL]
      apply ht
      have hk := k.2
      have hi : i.val ≤ j.val := hij
      change i.val+k.val+1 ≤ j.val
      dsimp [d] at hk
      omega
    exact abelianInterval_simple_ternary_weight B L
      (t.chain q.castSucc).val (t.chain q.succ).val hlo (t.chain.step q).le hhi
  have h := subgroupSeries_ternary_valuation_le_length d f hf he
  have h0 : f 0=B := by
    have he0:e 0=i := Fin.ext (Nat.add_zero _)
    simpa only [f,he0] using hB
  have hl : f (Fin.last d)=L := by
    have hel:e (Fin.last d)=j := by
      apply Fin.ext
      change i.val+(j.val-i.val)=j.val
      omega
    simpa only [f,hel] using hL
  rw [h0,hl,←normalChainQuotient_card B L] at h
  exact h

/-- A genuine composition refinement bounds the chosen chief weight.
Only abelian intervals use an order valuation; every nonabelian original
factor contributes zero even when its order is divisible by three. -/
theorem actualChiefWeight_le_compositionLength (s:ActualChiefSeries R)
    (t:SubnormalCompositionSeries R)
    (j:Fin (s.length+1)↪Fin (t.chain.length+1))
    (he:∀i,(t.chain (j i)).val=s.subgroup i)
    (h0:j 0=0) (hl:j (Fin.last s.length)=Fin.last t.chain.length) :
    actualChiefSeriesTernaryWeight s ≤ t.chain.length := by
  classical
  have hj : StrictMono j := by
    intro a b hab
    apply (compositionSeries_strictMono t).lt_iff_lt.mp
    rw [he,he]
    exact actualChiefSeries_strictMono s hab
  let z (i:Fin (s.length+1)) : ℕ := (j i).val
  have hi (i:Fin s.length) :
      chiefTernaryWeight (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ)) ≤ 
        z i.succ-z i.castSucc := by
    by_cases hab:IsMulCommutative
      (normalChainQuotient (s.subgroup i.castSucc) (s.subgroup i.succ))
    · letI := hab
      rw [chiefTernaryWeight,if_pos hab]
      exact compositionSeries_abelian_interval t (j i.castSucc) (j i.succ)
        (hj.monotone (Fin.castSucc_le_succ i)) _ _ (he _) (he _)
    · rw [chiefTernaryWeight_nonabelian _ hab]
      exact Nat.zero_le _
  have hz (i:Fin s.length) : (z i.succ-z i.castSucc)+z i.castSucc=z i.succ :=
    Nat.sub_add_cancel (hj.monotone (Fin.castSucc_le_succ i))
  have hsum : (∑i:Fin s.length,(z i.succ-z i.castSucc))+
      (∑i:Fin s.length,z i.castSucc)=(∑i:Fin s.length,z i.succ) := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _=>hz i)
  have htel : z 0+(∑i:Fin s.length,z i.succ)=
      (∑i:Fin s.length,z i.castSucc)+z (Fin.last s.length) :=
    (Fin.sum_univ_succ z).symm.trans (Fin.sum_univ_castSucc z)
  have hz0 : z 0=0 := congrArg Fin.val h0
  have hzl : z (Fin.last s.length)=t.chain.length := congrArg Fin.val hl
  have hgap : (∑i:Fin s.length,(z i.succ-z i.castSucc))=t.chain.length := by omega
  calc
    actualChiefSeriesTernaryWeight s ≤ ∑i:Fin s.length,(z i.succ-z i.castSucc) :=
      Finset.sum_le_sum (fun i _=>hi i)
    _=t.chain.length := hgap

/-- Existence of a sufficiently long actual composition series is
proved, so a published bound on composition length can be applied
without importing an abstract a₃-invariance hypothesis. -/
theorem actualChiefWeight_le_some_compositionLength (s:ActualChiefSeries R) :
    ∃t:SubnormalCompositionSeries R,actualChiefSeriesTernaryWeight s ≤ t.chain.length := by
  obtain ⟨t,j,he,h0,hl⟩ := actualChiefSeries_composition_refinement s
  exact ⟨t,actualChiefWeight_le_compositionLength s t j he h0 hl⟩

end SymmetricSubgroupAsymptotics
