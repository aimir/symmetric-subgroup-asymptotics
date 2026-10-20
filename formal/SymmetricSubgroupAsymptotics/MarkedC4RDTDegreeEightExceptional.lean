import SymmetricSubgroupAsymptotics.MarkedC4RDTExcessStructure

/-! Exact ordinary exceptional implication used in RDT Proposition 7.4,
Case IIa (p.25), from Theorem 5.7(i) (p.18), arXiv:2503.05416.
For an ORIGINAL excessive transitive binary group of degree eight, a
nonabelian actual normal quotient forces N=1 and has the displayed exact
centralizer/commutator invariants. This is an unmarked structural input;
there is no subgroup count, source rank, or project capacity assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.MarkedC4.RDTDegreeEightExceptional
open RDTExcessStructure ActualNormalFMarkedPeel

/-- The degree-eight forcing direction explicitly used at p.25, rather
than the weaker existential disjunction common to all of Theorem5.7. -/
def PublishedDegreeEightExceptional : Prop :=
  ∀ (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))),n=8 →IsPGroup 2 G →
    (∀ x y : Fin n,∃ g : G,g.val x=y) →HasExcess G n 2 →
    ∀ (N : Subgroup G) [N.Normal],(¬∀ x y : G ⧸ N,x*y=y*x) →
      N=⊥ ∧ centralLog (⊤ : Subgroup (G ⧸ N))=1 ∧
        commutatorLog (⊤ : Subgroup (G ⧸ N))+
          3*centralLog (⊤ : Subgroup (G ⧸ N))=4

/-- Bind that ordinary implication to the ACTUAL quotient target and
its actual full normal subgroup, retaining the coefficient three. -/
theorem exceptional_packet (lit : PublishedDegreeEightExceptional)
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (hn : n=8)
    (hG : IsPGroup 2 G) (htrans : ∀ x y : Fin n,∃ g : G,g.val x=y)
    (hexcess : HasExcess G n 2) (N : Subgroup G) [N.Normal]
    (hnonab : ¬∀ x y : G ⧸ N,x*y=y*x) :
    N=⊥ ∧ ∃ F : Subgroup (G ⧸ N),F.Normal ∧ F=⊤ ∧
      commutatorLog F+3*centralLog F≤(n : ℝ)/2 ∧
        centralLog F≤(n : ℝ)/4 := by
  obtain ⟨hN,hcentral,hcomm⟩ := lit n G hn hG htrans hexcess N hnonab
  refine ⟨hN,⊤,inferInstance,rfl,?_,?_⟩
  · rw [hcomm,hn]
    norm_num
  · rw [hcentral,hn]
    norm_num

end SymmetricSubgroupAsymptotics.MarkedC4.RDTDegreeEightExceptional
