import SymmetricSubgroupAsymptotics.MarkedC4RDTExcessStructure
import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank

/-! Ordinary RDT5.5(ii) on original transitive factors, with a literal
maximal fully projecting tail. Quotients are used only through onto maps. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.RDTOriginalWordStructure
open RDTExcessStructure ActualGlobalMarkGeneratorRank ActualMarkZeroNormalRank

def tailProjection {t : ℕ} (K : Fin t → Type) [∀ i,Group (K i)]
    (L : Subgroup (∀ i,K i)) (tail : Finset (Fin t)) : L →* ∀ i : {j // j∈tail},K i.val where
  toFun x i := x.val i.val
  map_one' := rfl
  map_mul' _ _ := rfl

def MaximalTail {t : ℕ} (K : Fin t → Type) [∀ i,Group (K i)]
    (L : Subgroup (∀ i,K i)) (tail : Finset (Fin t)) : Prop :=
  Function.Surjective (tailProjection K L tail) ∧
    ∀ S : Finset (Fin t),Function.Surjective (tailProjection K L S) →S.card≤tail.card

def dependentDegree {t : ℕ} (n : Fin t → ℕ) (tail : Finset (Fin t)) : ℝ :=
  ∑ i : Fin t,if i∈tail then 0 else (n i : ℝ)
def tailDegree {t : ℕ} (n : Fin t → ℕ) (tail : Finset (Fin t)) : ℝ :=
  ∑ i : Fin t,if i∈tail then (n i : ℝ) else 0

/-- Only original permutation factors occur in this ordinary input.
The three absence hypotheses are the literal hypotheses of RDT5.5(ii). -/
def PublishedTheorem55Binary : Prop :=
  ∀ (t : ℕ) (n : Fin t → ℕ) (K : ∀ i,Subgroup (Equiv.Perm (Fin (n i)))),
    (∀ i,IsPGroup 2 (K i)) →
    (∀ i,∀ x y : Fin (n i),∃ g : K i,g.val x=y) →
    ∀ L : Subgroup (∀ i,K i),
    (∀ i,Function.Surjective ((Pi.evalMonoidHom (fun j => K j) i).comp L.subtype)) →
    ∀ tail : Finset (Fin t),MaximalTail (fun i => K i) L tail →
    ∀ N : Subgroup L,N.Normal →
      (normalGen N : ℝ)≤(3/8)*dependentDegree n tail+tailDegree n tail/2 ∧
      ((∀ i,i∉tail →¬(HasExcess (K i) (n i) 2 ∧ n i=8)) →
        (normalGen N : ℝ)≤(5/16)*dependentDegree n tail+tailDegree n tail/2) ∧
      ((∀ i,i∉tail →¬HasExcess (K i) (n i) 2) →
        (normalGen N : ℝ)≤dependentDegree n tail/4+tailDegree n tail/2)

/-- The ordinary original-word generator bound descends through the
actual quotient map, then adds the single global marking cost r. -/
theorem marked_quotient_rank_bounds
    (lit : PublishedTheorem55Binary)
    (t : ℕ) (n : Fin t → ℕ) (K : ∀ i,Subgroup (Equiv.Perm (Fin (n i))))
    (hK : ∀ i,IsPGroup 2 (K i))
    (htrans : ∀ i,∀ x y : Fin (n i),∃ g : K i,g.val x=y)
    (L : Subgroup (∀ i,K i)) [Group.IsNilpotent L]
    (hfull : ∀ i,Function.Surjective ((Pi.evalMonoidHom (fun j => K j) i).comp L.subtype))
    (tail : Finset (Fin t)) (hmax : MaximalTail (fun i => K i) L tail)
    {B : Type} [Group B] [Finite B] (r : ℕ) (A : Subgroup (B × Marks r))
    (q : L →* PhysicalImage A) (hq : Function.Surjective q) :
    (genRank A : ℝ)≤(3/8)*dependentDegree n tail+tailDegree n tail/2+r ∧
      ((∀ i,i∉tail →¬(HasExcess (K i) (n i) 2 ∧ n i=8)) →
        (genRank A : ℝ)≤(5/16)*dependentDegree n tail+tailDegree n tail/2+r) ∧
      ((∀ i,i∉tail →¬HasExcess (K i) (n i) 2) →
        (genRank A : ℝ)≤dependentDegree n tail/4+tailDegree n tail/2+r) := by
  have hord := lit t n K hK htrans L hfull tail hmax ⊤ inferInstance
  have hn : (genRank L : ℝ)≤normalGen (⊤ : Subgroup L) := by
    exact_mod_cast genRank_le_normalGen_top (G := L)
  have hqrank := genRank_le_of_surjective q hq
  have hmarked := genRank_le_physical_add_marks r A
  have htotal : genRank A≤genRank L+r := hmarked.trans (Nat.add_le_add_right hqrank r)
  have hreal : (genRank A : ℝ)≤(genRank L : ℝ)+r := by exact_mod_cast htotal
  have transfer (c : ℝ) (hc : (normalGen (⊤ : Subgroup L) : ℝ)≤c) :
      (genRank A : ℝ)≤c+r := by linarith
  exact ⟨transfer _ hord.1,fun h => transfer _ (hord.2.1 h),
    fun h => transfer _ (hord.2.2 h)⟩

end SymmetricSubgroupAsymptotics.MarkedC4.RDTOriginalWordStructure
