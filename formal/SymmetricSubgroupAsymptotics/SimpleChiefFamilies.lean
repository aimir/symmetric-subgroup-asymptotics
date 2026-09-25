import SymmetricSubgroupAsymptotics.ChiefTernaryWeights
import SymmetricSubgroupAsymptotics.NormalImageQuotient
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic.FinCases

/-! Symbolic actual chief chains for all nonabelian simple groups and
for their original index-two extensions. Natural alternating and symmetric
actions are covered uniformly without enumerating their group elements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative
namespace SymmetricSubgroupAsymptotics

theorem chiefTernaryWeight_congr {G Q:Type} [Group G] [Group Q] (e:G≃*Q) :
    chiefTernaryWeight G=chiefTernaryWeight Q := by
  have hc : IsMulCommutative G ↔ IsMulCommutative Q := by
    constructor
    · intro h
      letI := h
      refine ⟨⟨fun x y=>e.symm.injective ?_⟩⟩
      rw [map_mul,map_mul]
      exact mul_comm _ _
    · intro h
      letI := h
      refine ⟨⟨fun x y=>e.injective ?_⟩⟩
      rw [map_mul,map_mul]
      exact mul_comm _ _
  classical
  by_cases h:IsMulCommutative G
  · have hq := hc.mp h
    simp [chiefTernaryWeight,h,hq,Nat.card_congr e.toEquiv]
  · have hq:¬IsMulCommutative Q := fun hq=>h (hc.mpr hq)
    simp [chiefTernaryWeight,h,hq]

def normalChainQuotientBotEquiv {G:Type} [Group G] (N:Subgroup G) [N.Normal] :
    normalChainQuotient ⊥ N≃*N :=
  normalSectionQuotientEquiv N ⊥ (MonoidHom.id N) Function.surjective_id (by simp)

def simpleChiefSeries (G:Type) [Group G] [IsSimpleGroup G] : ActualChiefSeries G where
  length := 1
  subgroup := ![⊥,⊤]
  normal i := by
    fin_cases i
    · change (⊥:Subgroup G).Normal; infer_instance
    · change (⊤:Subgroup G).Normal; infer_instance
  head := rfl
  last := rfl
  step i := by fin_cases i; exact bot_lt_top
  chief i K hK _ _ := by fin_cases i; exact hK.eq_bot_or_eq_top

theorem simpleChiefSeries_weight (G:Type) [Group G] [IsSimpleGroup G]
    (hnc:¬IsMulCommutative G) : actualChiefSeriesTernaryWeight (simpleChiefSeries G)=0 := by
  change (∑i:Fin 1,chiefTernaryWeight
    (normalChainQuotient ((simpleChiefSeries G).subgroup i.castSucc)
      ((simpleChiefSeries G).subgroup i.succ)))=0
  rw [Fin.sum_univ_one]
  change chiefTernaryWeight (normalChainQuotient (⊥:Subgroup G) ⊤)=0
  rw [chiefTernaryWeight_congr ((normalChainQuotientBotEquiv (⊤:Subgroup G)).trans
    (Subgroup.topEquiv)),chiefTernaryWeight_nonabelian G hnc]

section IndexTwo
variable {G:Type} [Group G] (N:Subgroup G) [N.Normal] [IsSimpleGroup N]
variable (hindex:N.index=2)
include hindex

theorem indexTwo_simple_normal_minimal (K:Subgroup G) (hK:K.Normal) (hKN:K ≤ N) :
    K=⊥ ∨ K=N := by
  letI := hK
  exact (Subgroup.isSimpleGroup_iff.mp (inferInstance: IsSimpleGroup N)).2 K hKN inferInstance

theorem indexTwo_maximal (K:Subgroup G) (hNK:N ≤ K) : K=N ∨ K=⊤ := by
  have hm := Subgroup.relIndex_mul_index hNK
  rw [hindex] at hm
  have hd : K.index∣2 := ⟨N.relIndex K,by simpa [Nat.mul_comm] using hm.symm⟩
  rcases Nat.dvd_prime Nat.prime_two |>.mp hd with h|h
  · exact Or.inr (Subgroup.index_eq_one.mp h)
  · left
    have hr:N.relIndex K=1 := by rw [h] at hm; omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hr) hNK

/-- Literal three-term original chief chain, with original simple normal
subgroup retained as the middle term. -/
def indexTwoSimpleChiefSeries : ActualChiefSeries G where
  length := 2
  subgroup := ![⊥,N,⊤]
  normal i := by
    fin_cases i
    · change (⊥:Subgroup G).Normal; infer_instance
    · change N.Normal; infer_instance
    · change (⊤:Subgroup G).Normal; infer_instance
  head := rfl
  last := rfl
  step i := by
    fin_cases i
    · exact (Subgroup.isSimpleGroup_iff.mp (inferInstance:IsSimpleGroup N)).1.bot_lt
    · change N<⊤
      apply lt_top_iff_ne_top.mpr
      intro h
      rw [h,Subgroup.index_top] at hindex
      omega
  chief i K hK hlo hhi := by
    fin_cases i
    · exact indexTwo_simple_normal_minimal N hindex K hK hhi
    · exact indexTwo_maximal N hindex K hlo

theorem indexTwoSimpleChiefSeries_weight [Finite G] (hnc:¬IsMulCommutative N) :
    actualChiefSeriesTernaryWeight (indexTwoSimpleChiefSeries N hindex)=0 := by
  change (∑i:Fin 2,chiefTernaryWeight
    (normalChainQuotient ((indexTwoSimpleChiefSeries N hindex).subgroup i.castSucc)
      ((indexTwoSimpleChiefSeries N hindex).subgroup i.succ)))=0
  rw [Fin.sum_univ_two]
  change chiefTernaryWeight (normalChainQuotient (⊥:Subgroup G) N)+
    chiefTernaryWeight (normalChainQuotient N (⊤:Subgroup G))=0
  rw [chiefTernaryWeight_congr (normalChainQuotientBotEquiv N),
    chiefTernaryWeight_nonabelian N hnc]
  have hc:Nat.Coprime (Nat.card (normalChainQuotient N (⊤:Subgroup G))) 3 := by
    have hord : Nat.card (normalChainQuotient N (⊤:Subgroup G))=N.index := by
      have h := Subgroup.relIndex_ker (⊤:Subgroup G) (QuotientGroup.mk' N)
      simpa only [QuotientGroup.ker_mk',normalChainQuotient,Subgroup.relIndex_top_right]
        using h.symm
    rw [hord,hindex]
    decide
  rw [chiefTernaryWeight_coprime _ hc]

end IndexTwo

/-- All natural alternating groups in degree at least five have an
actual zero-ternary-weight chief chain. -/
theorem alternatingChiefSeries_zero (n:ℕ) (hn:5 ≤ n) :
    ∃s:ActualChiefSeries (alternatingGroup (Fin n)),actualChiefSeriesTernaryWeight s=0 := by
  letI := alternatingGroup.isSimpleGroup (α:=Fin n) (by simpa using hn)
  have hnc:¬IsMulCommutative (alternatingGroup (Fin n)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simpa using (show ¬n ≤ 3 by omega)
  exact ⟨simpleChiefSeries _,simpleChiefSeries_weight _ hnc⟩

/-- All natural symmetric groups in degree at least five have the
literal chief chain 1<A_n<S_n and zero ternary weight. -/
theorem symmetricChiefSeries_zero (n:ℕ) (hn:5 ≤ n) :
    ∃s:ActualChiefSeries (Equiv.Perm (Fin n)),actualChiefSeriesTernaryWeight s=0 := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  letI := alternatingGroup.isSimpleGroup (α:=Fin n) (by simpa using hn)
  have hnc:¬IsMulCommutative (alternatingGroup (Fin n)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    simpa using (show ¬n ≤ 3 by omega)
  exact ⟨indexTwoSimpleChiefSeries (alternatingGroup (Fin n)) alternatingGroup.index_eq_two,
    indexTwoSimpleChiefSeries_weight _ alternatingGroup.index_eq_two hnc⟩

end SymmetricSubgroupAsymptotics
