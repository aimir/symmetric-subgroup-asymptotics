import SymmetricSubgroupAsymptotics.MarkedC4ActualRawProjectionHistory
import SymmetricSubgroupAsymptotics.MarkedC4ActualCaseIITargetStructure
import SymmetricSubgroupAsymptotics.MarkedC4ActualTableauPeeling

/-! Actual excessive-factor selection on the original raw projection
history. Original excess-two degree-eight factors take first priority;
then original excess two; then original excess one. Abelian CURRENT
quotients receive priority zero and belong to the single abelian block. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualExcessHistorySelection
open ActualPeelNormalChains RDTExcessStructure ActualCaseIITargetStructure

variable {t : ℕ} (degree : Fin t → ℕ)
  (G : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
  (M : Type) [Group M]
  (J : Subgroup ((∀ i,G i) × M))
  (hfull : ∀ i,Function.Surjective (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) J i))

instance stageNormal (S : Finset (Fin t)) (i : Fin t) :
    (ActualPeelNormalChains.factor (fun j => ↥(G j)) J S i).Normal := ActualPeelNormalChains.factor_normal (fun j => ↥(G j)) J hfull S i
def Quotient (degree : Fin t → ℕ)
    (G : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
    (M : Type) [Group M] (J : Subgroup ((∀ i,G i) × M))
    (hfull : ∀ i,Function.Surjective
      (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) J i))
    (S : Finset (Fin t)) (i : Fin t) : Type :=
  G i ⧸ ActualPeelNormalChains.factor (fun j => ↥(G j)) J S i

instance quotientGroup (S : Finset (Fin t)) (i : Fin t) :
    Group (Quotient degree G M J hfull S i) := by
  letI : (ActualPeelNormalChains.factor (fun j => ↥(G j)) J S i).Normal :=
    ActualPeelNormalChains.factor_normal (fun j => ↥(G j)) J hfull S i
  exact inferInstanceAs (Group (G i ⧸ ActualPeelNormalChains.factor (fun j => ↥(G j)) J S i))

instance quotientFinite (S : Finset (Fin t)) (i : Fin t) :
    Finite (Quotient degree G M J hfull S i) :=
  inferInstanceAs (Finite (G i ⧸ ActualPeelNormalChains.factor (fun j => ↥(G j)) J S i))

def Nonabelian (degree : Fin t → ℕ)
    (G : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
    (M : Type) [Group M] (J : Subgroup ((∀ i,G i) × M))
    (hfull : ∀ i,Function.Surjective
      (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) J i))
    (S : Finset (Fin t)) (i : Fin t) : Prop :=
  ¬∀ x y : Quotient degree G M J hfull S i,x*y=y*x

def BadQuarter (degree : Fin t → ℕ)
    (G : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
    (M : Type) [Group M] (J : Subgroup ((∀ i,G i) × M))
    (hfull : ∀ i,Function.Surjective
      (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) J i))
    (S : Finset (Fin t)) (i : Fin t) : Prop :=
  ∃ V : Subgroup (Quotient degree G M J hfull S i),
    V.Normal ∧ (degree i : ℝ)/4<(normalGen V : ℝ)

def priority (degree : Fin t → ℕ)
    (G : ∀ i,Subgroup (Equiv.Perm (Fin (degree i))))
    (M : Type) [Group M] (J : Subgroup ((∀ i,G i) × M))
    (hfull : ∀ i,Function.Surjective
      (ActualPeelNormalChains.coordinate (fun j => ↥(G j)) J i))
    (S : Finset (Fin t)) (i : Fin t) : ℕ :=
  if Nonabelian degree G M J hfull S i then
    if HasExcess (G i) (degree i) 2 then (if degree i=8 then 3 else 2)
    else if HasExcess (G i) (degree i) 1 ∧ BadQuarter degree G M J hfull S i then 1 else 0
  else 0

theorem exists_plan (S : Finset (Fin t)) :
    ∃ l,ActualTableauPeeling.Plan
      (fun i S => (priority degree G M J hfull S i : ℝ)) S l :=
  ActualTableauPeeling.exists_plan _ S

/-- A selected priority at most two excludes every nonabelian current
quotient of an original excess-two degree-eight factor in the source. -/
theorem no_excess_eight_of_max_le_two {S : Finset (Fin t)} {i : Fin t}
    (hmax : ∀ j∈S,priority degree G M J hfull S j≤priority degree G M J hfull S i)
    (hi : priority degree G M J hfull S i≤2) :
    ∀ j∈S,Nonabelian degree G M J hfull S j →¬(HasExcess (G j) (degree j) 2 ∧ degree j=8) := by
  intro j hj hn he
  have hp : priority degree G M J hfull S j=3 := by
    simp only [priority,if_pos hn,if_pos he.1,if_pos he.2]
  have hh := (hmax j hj).trans hi
  omega

/-- Priority at most one excludes all original excess-two factors from
nonabelian current quotients. This is the exact improved 5.5 condition
AFTER constructing the physical abelian block. -/
theorem no_excess_two_of_max_le_one {S : Finset (Fin t)} {i : Fin t}
    (hmax : ∀ j∈S,priority degree G M J hfull S j≤priority degree G M J hfull S i)
    (hi : priority degree G M J hfull S i≤1) :
    ∀ j∈S,Nonabelian degree G M J hfull S j →¬HasExcess (G j) (degree j) 2 := by
  intro j hj hn he
  have hp : 2≤priority degree G M J hfull S j := by
    rw [priority,if_pos hn,if_pos he]
    split_ifs <;> norm_num
  have hh := (hmax j hj).trans hi
  omega

/-- If the actual greedy residual has no positive priority, every
nonabelian quotient satisfies the ORIGINAL-degree normal quarter bound.
Thus the stopping family is the checked actual Case-I family. -/
theorem caseI_of_zero
    (h53 : PublishedProposition53Binary)
    (hn : ∀ i,2<degree i) (hG : ∀ i,IsPGroup 2 (G i))
    (htrans : ∀ i,∀ x y : Fin (degree i),∃ g : G i,g.val x=y)
    (S : Finset (Fin t))
    (hz : ∀ i∈S,priority degree G M J hfull S i=0) :
    ∀ i∈S,Nonabelian degree G M J hfull S i →
      ∀ V : Subgroup (Quotient degree G M J hfull S i),V.Normal →
        (normalGen V : ℝ)≤(degree i : ℝ)/4 := by
  intro i hi hnab V hV
  letI : V.Normal := hV
  by_contra hv
  have hlarge : (degree i : ℝ)/4<(normalGen V : ℝ) := lt_of_not_ge hv
  have hbad : BadQuarter degree G M J hfull S i := ⟨V,hV,hlarge⟩
  letI : (ActualPeelNormalChains.factor (fun j => ↥(G j)) J S i).Normal :=
    ActualPeelNormalChains.factor_normal (fun j => ↥(G j)) J hfull S i
  let q := QuotientGroup.mk' (ActualPeelNormalChains.factor (fun j => ↥(G j)) J S i)
  letI : (V.comap q).Normal := Subgroup.Normal.comap hV q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hm : (V.comap q).map q=V := by
    apply Subgroup.map_comap_eq_self
    rw [q.range_eq_top_of_surjective hq]
    exact le_top
  have hr : normalGen V≤normalGen (V.comap q) := by
    have hh := normalGen_map_le q hq (V.comap q)
    rw [hm] at hh
    exact hh
  have hrr : (normalGen V : ℝ)≤normalGen (V.comap q) := by exact_mod_cast hr
  obtain ⟨e,he,hexcess,_⟩ := h53 (degree i) (G i) (hn i) (hG i) (htrans i)
    ⟨V.comap q,inferInstance,lt_of_lt_of_le hlarge hrr⟩
  have hp := hz i hi
  rcases he with he|he
  · subst e
    by_cases htwo : HasExcess (G i) (degree i) 2
    · simp only [priority,if_pos hnab,if_pos htwo] at hp
      split_ifs at hp <;> omega
    · simp only [priority,if_pos hnab,if_neg htwo,if_pos (And.intro hexcess hbad)] at hp
      norm_num at hp
  · subst e
    simp only [priority,if_pos hnab,if_pos hexcess] at hp
    split_ifs at hp <;> omega

end SymmetricSubgroupAsymptotics.MarkedC4.ActualExcessHistorySelection
