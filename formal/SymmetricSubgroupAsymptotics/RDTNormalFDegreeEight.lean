import SymmetricSubgroupAsymptotics.RDTNormalFSmallEight
import SymmetricSubgroupAsymptotics.NormalFQuotientPacketTransport
import SymmetricSubgroupAsymptotics.RDTDegreeEightExceptionalProof
import SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEight26
import SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEight27
import SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEight28
import SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEight29
import SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEight30
import SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEight31
import SymmetricSubgroupAsymptotics.RDTNormalFQuotientsEightThirtyFive

/-! All original degree-eight normal-F packets. The original source and
literal normal denominator follow one actual quotient equivalence; the
proper-normal choice in the Sylow128 source is preserved. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.RDTNormalFDegreeEight
open MarkedC4 MarkedC4.RDTExcessStructure MarkedC4.ActualNormalFMarkedPeel
open RDTDegreeEightExceptionalTransport BinaryActionRegistry8

theorem excess_one_packet
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8,∃ g : G,g.val x=y)
    (hexcess : HasExcess G 8 1) (N : Subgroup G) [N.Normal]
    (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a)
    (hrank : genRank (G ⧸ N)=genRank G) :
    ∃ F : Subgroup (G ⧸ N),F.Normal ∧
      commutatorLog F+centralLog F≤4 ∧ centralLog F≤2 := by
  have ht : PermutationSubgroupTransitive G := by
    intro x y
    obtain ⟨g,hg⟩ := htrans x y
    exact ⟨g.val,g.property,hg⟩
  obtain ⟨i,g,hg⟩ := BinaryActionRegistry8.complete G hG ht
  let e := actionConjugacyEquiv g hg
  fin_cases i
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T1.generators))≤32
      rw [BinaryMenuCayley8T1.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T2.generators))≤32
      rw [BinaryMenuCayley8T2.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))≤32
      rw [BinaryMenuCayley8T3.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T4.generators))≤32
      rw [BinaryMenuCayley8T4.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T5.generators))≤32
      rw [BinaryMenuCayley8T5.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T6.generators))≤32
      rw [BinaryMenuCayley8T6.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T7.generators))≤32
      rw [BinaryMenuCayley8T7.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T8.generators))≤32
      rw [BinaryMenuCayley8T8.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T9.generators))≤32
      rw [BinaryMenuCayley8T9.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T10.generators))≤32
      rw [BinaryMenuCayley8T10.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T11.generators))≤32
      rw [BinaryMenuCayley8T11.exact_card]
      omega
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T15.generators))≤32
      rw [BinaryMenuCayley8T15.exact_card]
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T16.generators))≤32
      rw [BinaryMenuCayley8T16.exact_card]
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T17.generators))≤32
      rw [BinaryMenuCayley8T17.exact_card]
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T18.generators))≤32
      rw [BinaryMenuCayley8T18.exact_card]
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T19.generators))≤32
      rw [BinaryMenuCayley8T19.exact_card]
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T20.generators))≤32
      rw [BinaryMenuCayley8T20.exact_card]
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T21.generators))≤32
      rw [BinaryMenuCayley8T21.exact_card]
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · have hc : Nat.card G≤32 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (Subgroup.closure (Set.range BinaryMenuCayley8T22.generators))≤32
      rw [BinaryMenuCayley8T22.exact_card]
    exact RDTNormalFSmallEight.quotient_packet G hG htrans hc hexcess N hnonab hrank
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T26.group
    let eq := e.trans BinaryMenuCayley8T26.originalEquiv.symm
    have h := NormalFEquivalenceTransport.quotient_packet_of_equiv eq 1 4 2
      (fun M _ hm => by
        simpa only [one_mul] using RDTNormalFQuotientsEight26.quotient_packet M hm)
      N hnonab
    simpa only [one_mul] using h
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T27.group
    let eq := e.trans BinaryMenuCayley8T27.originalEquiv.symm
    have h := NormalFEquivalenceTransport.quotient_packet_of_equiv eq 1 4 2
      (fun M _ hm => by
        simpa only [one_mul] using RDTNormalFQuotientsEight27.quotient_packet M hm)
      N hnonab
    simpa only [one_mul] using h
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T28.group
    let eq := e.trans BinaryMenuCayley8T28.originalEquiv.symm
    have h := NormalFEquivalenceTransport.quotient_packet_of_equiv eq 1 4 2
      (fun M _ hm => by
        simpa only [one_mul] using RDTNormalFQuotientsEight28.quotient_packet M hm)
      N hnonab
    simpa only [one_mul] using h
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T29.group
    let eq := e.trans BinaryMenuCayley8T29.originalEquiv.symm
    have h := NormalFEquivalenceTransport.quotient_packet_of_equiv eq 1 4 2
      (fun M _ hm => by
        simpa only [one_mul] using RDTNormalFQuotientsEight29.quotient_packet M hm)
      N hnonab
    simpa only [one_mul] using h
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T30.group
    let eq := e.trans BinaryMenuCayley8T30.originalEquiv.symm
    have h := NormalFEquivalenceTransport.quotient_packet_of_equiv eq 1 4 2
      (fun M _ hm => by
        simpa only [one_mul] using RDTNormalFQuotientsEight30.quotient_packet M hm)
      N hnonab
    simpa only [one_mul] using h
  · letI : Group (FiniteGroupRow 64) := BinaryMenuCayley8T31.group
    let eq := e.trans BinaryMenuCayley8T31.originalEquiv.symm
    have h := NormalFEquivalenceTransport.quotient_packet_of_equiv eq 1 4 2
      (fun M _ hm => by
        simpa only [one_mul] using RDTNormalFQuotientsEight31.quotient_packet M hm)
      N hnonab
    simpa only [one_mul] using h
  · letI : Group (FiniteGroupRow 128) := BinaryMenuCayley8T35.group
    let eq := e.trans BinaryMenuCayley8T35.originalEquiv.symm
    have h := NormalFEquivalenceTransport.quotient_packet_of_equiv eq 1 4 2
      (fun M _ hm => by
        simpa only [one_mul] using RDTNormalFQuotientsEightThirtyFive.quotient_packet M hm)
      N hnonab
    simpa only [one_mul] using h

/-- The complete original degree-eight clause, including the exact
coefficient-three Heisenberg exception. -/
theorem target_packet
    (G : Subgroup (Equiv.Perm (Fin 8))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin 8,∃ g : G,g.val x=y)
    (i : ℕ) (hi : i=1 ∨ i=2) (hexcess : HasExcess G 8 i)
    (N : Subgroup G) [N.Normal] (hnonab : ¬∀ a b : G ⧸ N,a*b=b*a)
    (hrank : i = 1 → genRank (G ⧸ N) = genRank G) :
    ∃ (F : Subgroup (G ⧸ N)) (e : ℝ),F.Normal ∧
      ((i=2 ∧ (8 : ℕ)=8 ∧ N=⊥ ∧ F=⊤ ∧ e=3) ∨
        (i=1 ∧ e=1) ∨ (i=2 ∧ e=5/4)) ∧
      commutatorLog F+e*centralLog F≤(8 : ℝ)/2 ∧
      centralLog F≤(8 : ℝ)/4 := by
  rcases hi with rfl | rfl
  · obtain ⟨F,hF,hc,hz⟩ := excess_one_packet G hG htrans hexcess N hnonab (hrank rfl)
    refine ⟨F,1,hF,Or.inr (Or.inl ⟨rfl,rfl⟩),?_,?_⟩
    · norm_num only [one_mul, show (8 : ℝ)/2=4 by norm_num]
      exact hc
    · norm_num only [show (8 : ℝ)/4=2 by norm_num]
      exact hz
  · obtain ⟨hN,hz,hc⟩ := RDTDegreeEightExceptionalProof.publishedDegreeEightExceptional
      8 G rfl hG htrans hexcess N hnonab
    refine ⟨⊤,3,inferInstance,Or.inl ⟨rfl,rfl,hN,rfl,rfl⟩,?_,?_⟩
    · norm_num only [show (8 : ℝ)/2=4 by norm_num]
      exact le_of_eq hc
    · rw [hz]
      norm_num

end SymmetricSubgroupAsymptotics.RDTNormalFDegreeEight
