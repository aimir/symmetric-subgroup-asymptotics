import SymmetricSubgroupAsymptotics.MarkedC4ActualHistoryPriority
import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessHistoryUniversal

/-! Canonical actual target packet from a fixed original normal menu.
It depends only on G,N and the finite selected priority, so applies
uniformly to every source in one fixed history fibre. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalPriorityTarget
open ActualHistoryPriority RDTExcessStructure ActualCaseIITargetStructure
open RDTDegreeEightExceptional ActualNormalFMarkedPeel

theorem target_packet (h53 : PublishedProposition53Binary) (h57 : PublishedTheorem57Binary)
    (h8 : PublishedDegreeEightExceptional)
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin n,∃ g : G,g.val x=y)
    (N : {N : Subgroup G // N.Normal})
    (hp : 0<normalPriority n G N) :
    letI : N.val.Normal := N.property
    ∃ (F : Subgroup (G ⧸ N.val)) (e : ℝ),F.Normal ∧
      ((normalPriority n G N=3 ∧ e=3) ∨ (normalPriority n G N=2 ∧ e=5/4) ∨
        (normalPriority n G N=1 ∧ e=1)) ∧
      commutatorLog F+e*centralLog F≤(n : ℝ)/2 ∧ centralLog F≤(n : ℝ)/4 := by
  letI : N.val.Normal := N.property
  have hab : ¬∀ x y : G ⧸ N.val,x*y=y*x := by
    by_contra hh
    simp only [normalPriority,if_neg (not_not.mpr hh),Nat.lt_irrefl] at hp
  have hn : 2<n := SmallPermutationQuotient.two_lt_degree G
    (QuotientGroup.mk' N.val) (QuotientGroup.mk'_surjective N.val) hab
  by_cases htwo : HasExcess G n 2
  · by_cases hd : n=8
    · obtain ⟨_,F,hFn,_,hcomm,hcentral⟩ := exceptional_packet h8 n G hd hG htrans htwo N.val hab
      refine ⟨F,3,hFn,Or.inl ⟨?_,rfl⟩,hcomm,hcentral⟩
      simp only [normalPriority,if_pos hab,if_pos htwo,if_pos hd]
    · obtain ⟨F,e,hFn,hbranch,hcomm,hcentral⟩ :=
        h57 n G hn hG htrans 2 (Or.inr rfl) htwo N.val hab (by intro hh; norm_num at hh)
      have he : e=5/4 := by
        rcases hbranch with h|h|h
        · exact False.elim (hd h.2.1)
        · norm_num at h
        · exact h.2
      refine ⟨F,e,hFn,Or.inr (Or.inl ⟨?_,he⟩),hcomm,hcentral⟩
      simp only [normalPriority,if_pos hab,if_pos htwo,if_neg hd]
  · have hone : HasExcess G n 1 ∧
        ∃ V : Subgroup (G ⧸ N.val),V.Normal ∧ (n : ℝ)/4<(normalGen V : ℝ) := by
      by_contra hh
      simp only [normalPriority,if_pos hab,if_neg htwo,if_neg hh,Nat.lt_irrefl] at hp
    obtain ⟨V,hV,hlarge⟩ := hone.2
    obtain ⟨j,F,e,hj,hexcess,_,hFn,hbranch,hcomm,hcentral⟩ :=
      @exists_actual_target_packet h53 h57 n G hn hG htrans N.val N.property hab V hV hlarge
    have hj1 : j=1 := by
      rcases hj with hj|hj
      · exact hj
      · subst j
        exact False.elim (htwo hexcess)
    have he : e=1 := by
      rcases hbranch with h|h|h
      · omega
      · exact h.2
      · omega
    refine ⟨F,e,hFn,Or.inr (Or.inr ⟨?_,he⟩),hcomm,hcentral⟩
    simp only [normalPriority,if_pos hab,if_neg htwo,if_pos hone]

/-- Canonical Case-I stop condition for the SAME fixed quotient menu. -/
theorem quarter_of_zero (h53 : PublishedProposition53Binary)
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin n,∃ g : G,g.val x=y)
    (N : {N : Subgroup G // N.Normal}) (hz : normalPriority n G N=0) :
    letI : N.val.Normal := N.property
    (¬∀ x y : G ⧸ N.val,x*y=y*x) →
      ∀ V : Subgroup (G ⧸ N.val),V.Normal →(normalGen V : ℝ)≤(n : ℝ)/4 := by
  letI : N.val.Normal := N.property
  intro hab V hV
  letI : V.Normal := hV
  by_contra hv
  have hlarge : (n : ℝ)/4<(normalGen V : ℝ) := lt_of_not_ge hv
  let q := QuotientGroup.mk' N.val
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective N.val
  letI : (V.comap q).Normal := Subgroup.Normal.comap hV q
  have hn : 2<n := SmallPermutationQuotient.two_lt_degree G q hq hab
  have hm : (V.comap q).map q=V := by
    apply Subgroup.map_comap_eq_self
    rw [q.range_eq_top_of_surjective hq]
    exact le_top
  have hr : normalGen V≤normalGen (V.comap q) := by
    have hh := normalGen_map_le q hq (V.comap q)
    rw [hm] at hh
    exact hh
  have hrr : (normalGen V : ℝ)≤normalGen (V.comap q) := by exact_mod_cast hr
  obtain ⟨j,hj,hexcess,_⟩ := h53 n G hn hG htrans
    ⟨V.comap q,inferInstance,lt_of_lt_of_le hlarge hrr⟩
  rcases hj with hj|hj
  · subst j
    by_cases htwo : HasExcess G n 2
    · simp only [normalPriority,if_pos hab,if_pos htwo] at hz
      split_ifs at hz <;> omega
    · have hone : HasExcess G n 1 ∧
          ∃ W : Subgroup (G ⧸ N.val),W.Normal ∧ (n : ℝ)/4<(normalGen W : ℝ) :=
        ⟨hexcess,V,hV,hlarge⟩
      simp only [normalPriority,if_pos hab,if_neg htwo,if_pos hone] at hz
      norm_num at hz
  · subst j
    simp only [normalPriority,if_pos hab,if_pos hexcess] at hz
    split_ifs at hz <;> omega

end SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalPriorityTarget
