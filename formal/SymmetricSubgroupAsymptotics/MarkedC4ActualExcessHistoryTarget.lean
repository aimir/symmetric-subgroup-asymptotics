import SymmetricSubgroupAsymptotics.MarkedC4ActualExcessHistorySelection
import SymmetricSubgroupAsymptotics.MarkedC4RDTDegreeEightExceptional

/-! Bind the actual history priority to its actual ordinary 5.7 target.
Coefficient three uses the exact published degree-eight forcing fact;
coefficient one retains the actual excessive quotient witness. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualExcessHistoryTarget
open ActualExcessHistorySelection RDTExcessStructure ActualCaseIITargetStructure
open ActualNormalFMarkedPeel RDTDegreeEightExceptional

variable {t : ℕ} (degree : Fin t → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
  (M : Type) [Group M] (J : Subgroup ((∀ i,G i) × M))
  (hfull : ∀ i,Function.Surjective
    (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) J i))

theorem actual_target
    (h53 : PublishedProposition53Binary) (h57 : PublishedTheorem57Binary)
    (h8 : PublishedDegreeEightExceptional)
    (hn : ∀ i,2<degree i) (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (degree i),∃ g : G i,g.val x=y)
    (S : Finset (Fin t)) (i : Fin t)
    (hp : 0<priority degree G M J hfull S i) :
    ∃ (F : Subgroup (Quotient degree G M J hfull S i)) (e : ℝ),F.Normal ∧
      ((priority degree G M J hfull S i=3 ∧ e=3) ∨
       (priority degree G M J hfull S i=2 ∧ e=5/4) ∨
       (priority degree G M J hfull S i=1 ∧ e=1)) ∧
      commutatorLog F+e*centralLog F≤(degree i : ℝ)/2 ∧
        centralLog F≤(degree i : ℝ)/4 := by
  have hab : Nonabelian degree G M J hfull S i := by
    by_contra hh
    simp [priority,hh] at hp
  let N := ActualPeelNormalChains.factor (fun j => ↥(G j)) J S i
  letI : N.Normal := ActualPeelNormalChains.factor_normal (fun j => ↥(G j)) J hfull S i
  by_cases htwo : HasExcess (G i) (degree i) 2
  · by_cases hd : degree i=8
    · obtain ⟨_,F,hFn,hFtop,hcomm,hcentral⟩ :=
        exceptional_packet h8 (degree i) (G i) hd (hG i) (htrans i) htwo N hab
      refine ⟨F,3,hFn,Or.inl ⟨?_,rfl⟩,hcomm,hcentral⟩
      simp only [priority,if_pos hab,if_pos htwo,if_pos hd]
    · obtain ⟨F,e,hFn,hbranch,hcomm,hcentral⟩ :=
        h57 (degree i) (G i) (hn i) (hG i) (htrans i) 2 (Or.inr rfl) htwo N hab
          (by intro hh; norm_num at hh)
      have he : e=5/4 := by
        rcases hbranch with h|h|h
        · exact False.elim (hd h.2.1)
        · norm_num at h
        · exact h.2
      refine ⟨F,e,hFn,Or.inr (Or.inl ⟨?_,he⟩),hcomm,hcentral⟩
      simp only [priority,if_pos hab,if_pos htwo,if_neg hd]
  · have hone : HasExcess (G i) (degree i) 1 ∧ BadQuarter degree G M J hfull S i := by
      by_contra hh
      simp [priority,hab,htwo,hh] at hp
    obtain ⟨V,hV,hlarge⟩ := hone.2
    letI : V.Normal := hV
    obtain ⟨j,F,e,hj,hexcess,_,hFn,hbranch,hcomm,hcentral⟩ :=
      @exists_actual_target_packet h53 h57 (degree i) (G i) (hn i) (hG i) (htrans i)
        N inferInstance hab V hV hlarge
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
    simp [priority,hab,htwo,hone]

end SymmetricSubgroupAsymptotics.MarkedC4.ActualExcessHistoryTarget
