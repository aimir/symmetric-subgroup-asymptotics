import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalFMarkedPeel

/-! Exact ordinary structural input from RDT Definition5.1 and Theorem5.7.
Its groups are original transitive permutation groups and their literal
normal quotients. This input contains no marked groups or subgroup counts. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.RDTExcessStructure
open ActualNormalFMarkedPeel

/-- The maximum ordinary normal-generator excess, Definition5.1. -/
def HasExcess (G : Type) [Group G] [Finite G] (n i : ℕ) : Prop :=
  (∃ V : Subgroup G,V.Normal ∧ (normalGen V : ℝ)=(n : ℝ)/4+i) ∧
    ∀ V : Subgroup G,V.Normal →(normalGen V : ℝ)≤(n : ℝ)/4+i

/-- The common base-two-log inequalities of Theorem5.7, retaining its
three branches. The proper normal F and excess-one rank hypothesis remain. -/
def PublishedTheorem57Binary : Prop :=
  ∀ (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))),2<n →IsPGroup 2 G →
    (∀ x y : Fin n,∃ g : G,g.val x=y) →
    ∀ i : ℕ,(i=1 ∨ i=2) →HasExcess G n i →
    ∀ (N : Subgroup G) [N.Normal],
    (¬∀ x y : G ⧸ N,x*y=y*x) →
    (i=1 →genRank (G ⧸ N)=genRank G) →
    ∃ (F : Subgroup (G ⧸ N)) (e : ℝ),F.Normal ∧
      ((i=2 ∧ n=8 ∧ N=⊥ ∧ F=⊤ ∧ e=3) ∨ (i=1 ∧ e=1) ∨ (i=2 ∧ e=5/4)) ∧
      commutatorLog F+e*centralLog F≤(n : ℝ)/2 ∧
      centralLog F≤(n : ℝ)/4

/-- The actual normal subgroup from the published ordinary theorem is
chosen without specializing it to the whole quotient. -/
theorem exists_target_packet (lit : PublishedTheorem57Binary)
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (hn : 2<n) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin n,∃ g : G,g.val x=y)
    (i : ℕ) (hi : i=1 ∨ i=2) (hexcess : HasExcess G n i)
    (N : Subgroup G) [N.Normal] (hnonab : ¬∀ x y : G ⧸ N,x*y=y*x)
    (hrank : i=1 →genRank (G ⧸ N)=genRank G) :
    ∃ (F : Subgroup (G ⧸ N)) (e : ℝ),F.Normal ∧
      ((i=2 ∧ n=8 ∧ N=⊥ ∧ F=⊤ ∧ e=3) ∨ (i=1 ∧ e=1) ∨ (i=2 ∧ e=5/4)) ∧
      commutatorLog F+e*centralLog F≤(n : ℝ)/2 ∧
      centralLog F≤(n : ℝ)/4 :=
  lit n G hn hG htrans i hi hexcess N hnonab hrank

end SymmetricSubgroupAsymptotics.MarkedC4.RDTExcessStructure
