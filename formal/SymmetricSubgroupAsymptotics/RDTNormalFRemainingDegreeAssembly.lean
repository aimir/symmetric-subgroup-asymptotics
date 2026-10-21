import SymmetricSubgroupAsymptotics.BinaryExcessProposition53Proof
import SymmetricSubgroupAsymptotics.RDTNormalFDegreeFour
import SymmetricSubgroupAsymptotics.RDTNormalFDegreeEight
import SymmetricSubgroupAsymptotics.RDTNormalFSixteenExcessTwo

/-! Exact assembly boundary for the remaining normal-F proof. All degrees
other than sixteen and thirty-two are already discharged; the excess-two
sixteen-point clause is also supplied here by its proved theorem. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open MarkedC4 MarkedC4.RDTExcessStructure MarkedC4.ActualNormalFMarkedPeel

def BinaryNormalFTargetAtDegree (n : ℕ) : Prop :=
  ∀ (G : Subgroup (Equiv.Perm (Fin n))), IsPGroup 2 G  → 
    (∀ x y : Fin n,∃ g : G,g.val x = y)  → 
    ∀ i : ℕ,(i = 1  ∨  i = 2)  →  HasExcess G n i  → 
    ∀ (N : Subgroup G) [N.Normal],
    (¬∀ x y : G ⧸ N,x*y = y*x)  → 
    (i = 1  →  genRank (G ⧸ N)  =  genRank G)  → 
    ∃ (F : Subgroup (G ⧸ N)) (e : ℝ),F.Normal  ∧ 
      ((i = 2  ∧  n = 8  ∧  N = ⊥  ∧  F = ⊤  ∧  e = 3)  ∨  (i = 1  ∧  e = 1)  ∨  (i = 2  ∧  e = 5/4))  ∧ 
      commutatorLog F+e*centralLog F ≤ (n : ℝ)/2  ∧  centralLog F ≤ (n : ℝ)/4

def BinarySixteenExcessOneNormalF : Prop :=
  ∀ (G : Subgroup (Equiv.Perm (Fin 16))), IsPGroup 2 G  → 
    (∀ x y : Fin 16,∃ g : G,g.val x = y)  →  HasExcess G 16 1  → 
    ∀ (N : Subgroup G) [N.Normal],
    (¬∀ x y : G ⧸ N,x*y = y*x)  →  genRank (G ⧸ N)  =  genRank G  → 
    ∃ F : Subgroup (G ⧸ N),F.Normal  ∧ 
      commutatorLog F+centralLog F ≤ 8  ∧  centralLog F ≤ 4

theorem binaryNormalFTargetAtFour : BinaryNormalFTargetAtDegree 4 := by
  intro G hG _ i hi hexcess N _ hnonab _
  rcases hi with rfl | rfl
  · obtain ⟨F,hF,hc,hz⟩ := RDTNormalFDegreeFour.quotient_packet G hG N hnonab
    refine ⟨F,1,hF,Or.inr (Or.inl ⟨rfl,rfl⟩),?_,?_⟩  <;> norm_num at *  <;> assumption
  · obtain ⟨V,hV,hval⟩ := hexcess.1
    letI := hV
    have hVgroup := hG.to_subgroup V
    have hb := (normalGen_normalSubgroup_le_primeCharacterRank 2 V hVgroup).trans
      (permutationTwoGroup_primeCharacterRank_le V (Fin 4) hVgroup)
    norm_num only [Nat.card_fin] at hb
    have hbr : (normalGen V : ℝ) ≤ 2 := by exact_mod_cast hb
    norm_num at hval
    linarith

theorem binaryNormalFTargetAtSixteen_of_excessOne
    (h16 : BinarySixteenExcessOneNormalF) : BinaryNormalFTargetAtDegree 16 := by
  intro G hG htrans i hi hexcess N _ hnonab hrank
  rcases hi with rfl | rfl
  · obtain ⟨F,hF,hc,hz⟩ := h16 G hG htrans hexcess N hnonab (hrank rfl)
    refine ⟨F,1,hF,Or.inr (Or.inl ⟨rfl,rfl⟩),?_,?_⟩  <;> norm_num at *  <;> assumption
  · obtain ⟨F,hF,hc,hz⟩ := theorem57_degree_sixteen_excess_two G hG htrans hexcess N hnonab
    refine ⟨F,5/4,hF,Or.inr (Or.inr ⟨rfl,rfl⟩),?_,?_⟩  <;> norm_num at *  <;> assumption

/-- No further infinite-degree or small-degree obligation is hidden in
the two remaining local clauses. -/
theorem publishedTheorem57Binary_of_remaining_degree_clauses
    (h16 : BinarySixteenExcessOneNormalF)
    (h32 : BinaryNormalFTargetAtDegree 32) :
    PublishedTheorem57Binary := by
  intro n G hn hG htrans i hi hexcess N _ hnonab hrank
  obtain ⟨V,hV,hval⟩ := hexcess.1
  have hipos : (0 : ℝ)  <  (i : ℝ) := by rcases hi with rfl | rfl  <;> norm_num
  have hhigh : (n : ℝ)/4 < (normalGen V : ℝ) := by linarith
  obtain ⟨_,_,_,hdegree,_,_⟩ := publishedProposition53Binary_proved
    n G hn hG htrans ⟨V,hV,hhigh⟩
  letI : MulAction.IsPretransitive G (Fin n) := ⟨htrans⟩
  let x : Fin n := ⟨0,by omega⟩
  obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hG
    (MulAction.stabilizer G x) ⊤ le_top
  have hcard : n = 2 ^ s.length := by
    simpa only [Subgroup.relIndex_top_right,
      MulAction.index_stabilizer_of_transitive G x,Nat.card_fin] using s.relIndex
  have hlo : 2 ≤ s.length := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : s.length ≤ 1)
    rw [←hcard] at hp
    norm_num at hp
    omega
  have hup : s.length ≤ 5 := by
    by_contra hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 6 ≤ s.length)
    rw [←hcard] at hp
    norm_num at hp
    omega
  have hdegrees : n = 4  ∨  n = 8  ∨  n = 16  ∨  n = 32 := by
    have hs : s.length = 2  ∨  s.length = 3  ∨  s.length = 4  ∨  s.length = 5 := by omega
    rcases hs with hs | hs | hs | hs  <;> rw [hs] at hcard  <;> norm_num at hcard  <;> omega
  rcases hdegrees with rfl | rfl | rfl | rfl
  · exact binaryNormalFTargetAtFour G hG htrans i hi hexcess N hnonab hrank
  · exact RDTNormalFDegreeEight.target_packet G hG htrans i hi hexcess N hnonab hrank
  · exact binaryNormalFTargetAtSixteen_of_excessOne h16 G hG htrans i hi hexcess N hnonab hrank
  · exact h32 G hG htrans i hi hexcess N hnonab hrank

end SymmetricSubgroupAsymptotics
