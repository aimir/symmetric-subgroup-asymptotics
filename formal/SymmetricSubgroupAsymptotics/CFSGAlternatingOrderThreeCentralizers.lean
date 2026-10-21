import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.Index

/-! Exact centralizer factors for actual order-three elements in A_n.
Their full symmetric centralizers always contain odd permutations when
n≥5, including the repeated-three-cycle case. Thus the alternating
centralizer has exactly half the full centralizer order. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingOrderThreeCentralizers
abbrev A (n : ℕ) := alternatingGroup (Fin n)

def centralizerSubtypeEquiv (n : ℕ) (g : A n) :
    Subgroup.centralizer ({g} : Set (A n)) ≃
      (alternatingGroup (Fin n)).subgroupOf
        (Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin n)))) where
  toFun x := ⟨⟨x.val.val,by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.property)⟩,x.val.property⟩
  invFun y := ⟨⟨y.val.val,y.property⟩,by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp y.val.property⟩
  left_inv x := by apply Subtype.ext;apply Subtype.ext;rfl
  right_inv y := by apply Subtype.ext;apply Subtype.ext;rfl

theorem centralizer_not_le_alternating_of_type (n : ℕ) (hn : 5≤n)
    (g : Equiv.Perm (Fin n)) (k : ℕ) (hk : 1≤k)
    (htype : g.cycleType=Multiset.replicate k 3) :
    ¬Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n)))≤alternatingGroup (Fin n) := by
  intro hle
  obtain ⟨_,hfixed,hcount⟩ := Equiv.Perm.centralizer_le_alternating_iff.mp hle
  have hk1 : k≤1 := by simpa only [htype,Multiset.count_replicate,if_pos rfl] using hcount 3
  have he : k=1 := by omega
  simp only [htype,Multiset.sum_replicate,smul_eq_mul,Fintype.card_fin] at hfixed
  rw [he] at hfixed
  norm_num at hfixed
  omega

theorem twice_alternating_centralizer_card (n : ℕ) (hn : 5≤n) (g : A n)
    (k : ℕ) (hk : 1≤k) (htype : g.val.cycleType=Multiset.replicate k 3) :
    2*Nat.card (Subgroup.centralizer ({g} : Set (A n)))=
      Nat.card (Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin n)))) := by
  letI : Nontrivial (Fin n) := Finite.one_lt_card_iff_nontrivial.mp
    (by simp only [Nat.card_fin];omega)
  let C := Subgroup.centralizer ({g.val} : Set (Equiv.Perm (Fin n)))
  have hnot : ¬C≤alternatingGroup (Fin n) := centralizer_not_le_alternating_of_type n hn g.val k hk htype
  have hd : (alternatingGroup (Fin n)).relIndex C∣2 := by
    simpa only [alternatingGroup.index_eq_two] using
      (alternatingGroup (Fin n)).relIndex_dvd_index_of_normal C
  have hi : (alternatingGroup (Fin n)).relIndex C=2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h|h
    · exact (hnot (Subgroup.relIndex_eq_one.mp h)).elim
    · exact h
  have hc := ((alternatingGroup (Fin n)).subgroupOf C).card_mul_index
  change Nat.card ((alternatingGroup (Fin n)).subgroupOf C)*
    (alternatingGroup (Fin n)).relIndex C=Nat.card C at hc
  rw [hi,←Nat.card_congr (centralizerSubtypeEquiv n g)] at hc
  simpa only [Nat.mul_comm] using hc

theorem symmetric_centralizer_card_of_type (n : ℕ) (g : Equiv.Perm (Fin n))
    (k : ℕ) (hk : 1≤k) (htype : g.cycleType=Multiset.replicate k 3) :
    Nat.card (Subgroup.centralizer ({g} : Set (Equiv.Perm (Fin n))))=
      3^k*k.factorial*(n-3*k).factorial := by
  rw [Equiv.Perm.nat_card_centralizer,htype]
  simp [Nat.ne_of_gt (show 0<k from by omega),Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]

theorem alternating_centralizer_factor (n : ℕ) (hn : 5≤n) (g : A n)
    (k : ℕ) (hk : 1≤k) (htype : g.val.cycleType=Multiset.replicate k 3) :
    2*Nat.card (Subgroup.centralizer ({g} : Set (A n)))=
      3^k*k.factorial*(n-3*k).factorial := by
  rw [twice_alternating_centralizer_card n hn g k hk htype,
    symmetric_centralizer_card_of_type n g.val k hk htype]

/-- An actual order-three element supplies its own cycle multiplicity,
actual support bound and exact alternating centralizer factor. -/
theorem order_three_profile (n : ℕ) (hn : 5≤n) (g : A n) (hg : orderOf g.val=3) :
    ∃ k : ℕ,1≤k ∧ 3*k≤n ∧ g.val.cycleType=Multiset.replicate k 3 ∧
      2*Nat.card (Subgroup.centralizer ({g} : Set (A n)))=
        3^k*k.factorial*(n-3*k).factorial := by
  obtain ⟨j,hj⟩ := Equiv.Perm.cycleType_prime_order
    (show (orderOf g.val).Prime by rw [hg];decide)
  have ht : g.val.cycleType=Multiset.replicate (j+1) 3 := by simpa only [hg] using hj
  have hs := g.val.support.card_le_univ
  rw [←g.val.sum_cycleType,ht] at hs
  have hb : 3*(j+1)≤n := by
    simpa only [Multiset.sum_replicate,smul_eq_mul,Fintype.card_fin,Nat.mul_comm] using hs
  exact ⟨j+1,by omega,hb,ht,alternating_centralizer_factor n hn g (j+1) (by omega) ht⟩

end SymmetricSubgroupAsymptotics.CFSGAlternatingOrderThreeCentralizers
