import SymmetricSubgroupAsymptotics.MarkedC4ActualQuotientMarkedNormalBudget

/-! Ordinary derived-normal quarter bound used verbatim in the proof of
RDT Theorem5.5(iii), p.17, arXiv:2503.05416, from Proposition5.3(i), p.16.
For a NONABELIAN original transitive binary Gi and N≤Gi', the proof states
|Gi:N|>2 and concludes d_Gi(N)≤ni/4. Abelian originals are handled here
by their trivial derived subgroup. No quotient/marked capacity is input. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.RDTDerivedNormalQuarter

/-- Exact unmarked ordinary corollary in the published proof5.5(iii). -/
def PublishedDerivedNormalQuarterBinary : Prop :=
  ∀ (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))),2<n →IsPGroup 2 G →
    (∀ x y : Fin n,∃ g : G,g.val x=y) →(¬∀ x y : G,x*y=y*x) →
    ∀ N : Subgroup G,N.Normal →N≤commutator G →
      (normalGen N : ℝ)≤(n : ℝ)/4

theorem original_bound (lit : PublishedDerivedNormalQuarterBinary)
    (n : ℕ) (G : Subgroup (Equiv.Perm (Fin n))) (hn : 2<n) (hG : IsPGroup 2 G)
    (htrans : ∀ x y : Fin n,∃ g : G,g.val x=y)
    (N : Subgroup G) (hN : N.Normal) (hderived : N≤commutator G) :
    (normalGen N : ℝ)≤(n : ℝ)/4 := by
  by_cases hab : ∀ x y : G,x*y=y*x
  · letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hab }
    have hc : commutator G=⊥ := commutator_eq_bot G
    have hbot : N=⊥ := bot_unique (hderived.trans_eq hc)
    rw [hbot,normalGen_bot,Nat.cast_zero]
    positivity
  · exact lit n G hn hG htrans hab N hN hderived

/-- The previously project-level original-normal premise is now supplied
by the named ordinary corollary. The quotient maps, actual physical source,
its derived normals and SAME global abelian mark remain constructed. -/
theorem actual_marked_budget (lit : PublishedDerivedNormalQuarterBinary)
    {t : ℕ} (n : Fin t → ℕ)
    (G : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (hn : ∀ i,2<n i) (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : G i,g.val x=y)
    (F : Fin t → Type) [∀ i,Group (F i)] [∀ i,Finite (F i)]
    (q : ∀ i,G i →* F i) (onto : ∀ i,Function.Surjective (q i))
    (M : Type) [CommGroup M] [Finite M]
    (A : Subgroup ((∀ i,F i) × M)) (tail : Finset (Fin t))
    (hfull : ∀ i,Function.Surjective
      ((Pi.evalMonoidHom F i).comp (ActualMarkZeroNormalRank.physical A))) :
    ∀ U : Subgroup A,U.Normal →
      U≤commutator A ⊓ ((ActualQuotientMarkedNormalBudget.tailHom F A tail).comp
        (ActualMarkZeroNormalRank.projection A)).ker →
      normalGen U≤ActualQuotientMarkedNormalBudget.dN tail n := by
  apply ActualQuotientMarkedNormalBudget.marked_budget F A tail
    (fun i => ↥(G i)) q onto n
  · intro i N hN hderived
    exact original_bound lit (n i) (G i) (hn i) (hG i) (htrans i) N hN hderived
  · exact hfull

end SymmetricSubgroupAsymptotics.MarkedC4.RDTDerivedNormalQuarter
