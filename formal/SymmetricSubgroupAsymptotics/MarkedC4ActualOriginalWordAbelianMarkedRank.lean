import SymmetricSubgroupAsymptotics.MarkedC4RDTOriginalWordStructure
import SymmetricSubgroupAsymptotics.MarkedC4ActualAbelianPhysicalBlockRank

/-! Original nonabelian physical words plus an actual abelian physical
block supply the Case-II source-rank inequality, with one global marker. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalWordAbelianMarkedRank
open RDTOriginalWordStructure RDTExcessStructure ActualGlobalMarkGeneratorRank ActualMarkZeroNormalRank

theorem actual_source_rank
    (lit : PublishedTheorem55Binary)
    (t : ℕ) (n : Fin t → ℕ) (K : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (hK : ∀ i,IsPGroup 2 (K i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : K i,g.val x=y)
    (L : Subgroup (∀ i,K i)) [Group.IsNilpotent L]
    (hfull : ∀ i,Function.Surjective ((Pi.evalMonoidHom (fun j => K j) i).comp L.subtype))
    (tail : Finset (Fin t)) (hmax : MaximalTail (fun i => K i) L tail)
    {B : Type} [Group B] [Finite B]
    (C : Type) [CommGroup C] [Finite C] (hC : IsPGroup 2 C) (m r : ℕ)
    (hExp : HasExp2 C (2+m)) {a : ℝ}
    (hcard : (Nat.card C : ℝ)≤(2 : ℝ)^(a/2))
    (J : Subgroup (B × (C × Marks r)))
    (q : L →* PhysicalImage J) (hq : Function.Surjective q)
    (e : ℝ)
    (hbranch : e=3 ∨
      (e=5/4 ∧ ∀ i,i∉tail →¬(HasExcess (K i) (n i) 2 ∧ n i=8)) ∨
      (e=1 ∧ ∀ i,i∉tail →¬HasExcess (K i) (n i) 2)) :
    (genRank J : ℝ)≤e*dependentDegree n tail/4+(tailDegree n tail+a)/2+r := by
  have hord := lit t n K hK htrans L hfull tail hmax ⊤ inferInstance
  have hn : (genRank L : ℝ)≤normalGen (⊤ : Subgroup L) := by
    exact_mod_cast genRank_le_normalGen_top (G := L)
  have hqrank : (genRank (PhysicalImage J) : ℝ)≤genRank L := by
    exact_mod_cast genRank_le_of_surjective q hq
  have hJ := ActualAbelianPhysicalBlockRank.rank_le_physical_add_abelian_marks
    C hC m r hExp hcard J
  have hdep : 0≤dependentDegree n tail := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  rcases hbranch with h | ⟨h,hno⟩ | ⟨h,hno⟩
  · subst e
    have hL := hn.trans hord.1
    linarith
  · subst e
    have hL := hn.trans (hord.2.1 hno)
    linarith
  · subst e
    have hL := hn.trans (hord.2.2 hno)
    linarith

end SymmetricSubgroupAsymptotics.MarkedC4.ActualOriginalWordAbelianMarkedRank
