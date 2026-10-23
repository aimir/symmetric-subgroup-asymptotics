import SymmetricSubgroupAsymptotics.PrimeIndexOutsideCentralizerCard
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact fusion in a finite abelian prime-index extension. The
identity p*k(G)=|N|+(p^2-1)*|Z(G) intersect N| is obtained from actual
commuting pairs. It covers binary and ternary top groups uniformly,
without a splitting, order-p lift, character theorem or GM hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.PrimeIndexAbelianClassCount
open PrimeIndexAbelianCentralizers PrimeIndexOutsideCentralizerCard
variable {G : Type*} [Group G]

theorem sum_subgroup_add_complement [Fintype G] (N : Subgroup G) (f : G→ℕ) :
    (∑g : G,f g)=(∑n : N,f n.val)+∑x : {g : G // g∉N},f x.val := by
  have hh := Fintype.sum_equiv (Equiv.Set.sumCompl (N : Set G))
    (fun z=>f (Equiv.Set.sumCompl (N : Set G) z)) f (fun _=>rfl)
  simpa only [Fintype.sum_sum_type,Equiv.Set.sumCompl_apply_inl,
    Equiv.Set.sumCompl_apply_inr] using hh.symm

theorem sum_centralizer_card [Fintype G] :
    (∑g : G,Nat.card (Subgroup.centralizer {g}))=Nat.card (ConjClasses G)*Nat.card G := by
  calc
    (∑g : G,Nat.card (Subgroup.centralizer {g}))=
        ∑g : G,Nat.card {y : G // Commute g y} :=
      Finset.sum_congr rfl (fun g _=>(Nat.card_congr (partnerEquivCentralizer g)).symm)
    _=Nat.card ((g : G)×{y : G // Commute g y}) := Nat.card_sigma.symm
    _=Nat.card {z : G×G // Commute z.1 z.2} :=
      Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype Commute).symm
    _=Nat.card (ConjClasses G)*Nat.card G := card_comm_eq_card_conjClasses_mul_card G

theorem prime_index_abelian_class_count [Finite G] (N : Subgroup G) [N.Normal]
    [IsMulCommutative N] (p : ℕ) (hp : p.Prime) (hindex : N.index=p) :
    p*Nat.card (ConjClasses G)=Nat.card N+(p^2-1)*Nat.card (centralKernel N) := by
  letI : Fintype G := Fintype.ofFinite _
  let C := centralKernel N
  let D := {n : N // n∉C}
  let O := {g : G // g∉N}
  have hsumN : (∑n : N,Nat.card (Subgroup.centralizer {(n:G)}))=
      Nat.card C*Nat.card G+Nat.card D*Nat.card N := by
    rw [sum_subgroup_add_complement C]
    congr 1
    · calc
        (∑c : C,Nat.card (Subgroup.centralizer {((c:N):G)}))=∑_c : C,Nat.card G := by
          apply Finset.sum_congr rfl
          intro c _
          have hc : ((c:N):G)∈Subgroup.center G := c.property
          have ht : Subgroup.centralizer {((c:N):G)}=⊤ :=
            Subgroup.centralizer_eq_top_iff_subset.mpr (Set.singleton_subset_iff.mpr hc)
          rw [ht]
          exact Nat.card_congr Subgroup.topEquiv.toEquiv
        _=Nat.card C*Nat.card G := by
          simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
    · calc
        (∑d : D,Nat.card (Subgroup.centralizer {((d:N):G)}))=∑_d : D,Nat.card N := by
          apply Finset.sum_congr rfl
          intro d _
          rw [centralizer_eq_kernel_of_noncentral N p hp hindex d.val d.property]
        _=Nat.card D*Nat.card N := by
          simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
  have hsumO : (∑x : O,Nat.card (Subgroup.centralizer {x.val}))=Nat.card O*(p*Nat.card C) := by
    calc
      (∑x : O,Nat.card (Subgroup.centralizer {x.val}))=∑_x : O,p*Nat.card C :=
        Finset.sum_congr rfl (fun x _=>outside_centralizer_card_abelian N p hp hindex x.val x.property)
      _=Nat.card O*(p*Nat.card C) := by
        simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]
  have hwhole : Nat.card (ConjClasses G)*Nat.card G=
      Nat.card C*Nat.card G+Nat.card D*Nat.card N+Nat.card O*(p*Nat.card C) := by
    rw [←sum_centralizer_card,sum_subgroup_add_complement N,hsumN,hsumO]
  have hNpart : Nat.card C+Nat.card D=Nat.card N := by
    simpa only [Nat.card_sum] using Nat.card_congr (Equiv.Set.sumCompl (C : Set N))
  have hGpart : Nat.card N+Nat.card O=Nat.card G := by
    simpa only [Nat.card_sum] using Nat.card_congr (Equiv.Set.sumCompl (N : Set G))
  have hGN := N.card_mul_index
  rw [hindex] at hGN
  have hsub : p^2-1+1=p^2 := Nat.sub_add_cancel (by nlinarith [hp.two_le])
  have hscaled : Nat.card N*(p*Nat.card (ConjClasses G))=
      Nat.card N*(Nat.card N+(p^2-1)*Nat.card C) := by
    apply Nat.add_right_cancel (m:=Nat.card N*Nat.card C)
    calc
      Nat.card N*(p*Nat.card (ConjClasses G))+Nat.card N*Nat.card C =
          Nat.card (ConjClasses G)*Nat.card G+Nat.card N*Nat.card C := by
        rw [←hGN]
        ring
      _=Nat.card C*Nat.card G+Nat.card D*Nat.card N+
          Nat.card O*(p*Nat.card C)+Nat.card N*Nat.card C := by rw [hwhole]
      _=(Nat.card C+Nat.card D)*Nat.card N+
          (Nat.card N+Nat.card O)*(p*Nat.card C) := by
        rw [←hGN]
        ring
      _=Nat.card N*Nat.card N+Nat.card G*(p*Nat.card C) := by rw [hNpart,hGpart]
      _=Nat.card N*(Nat.card N+p^2*Nat.card C) := by
        rw [←hGN]
        ring
      _=Nat.card N*(Nat.card N+(p^2-1)*Nat.card C)+Nat.card N*Nat.card C := by
        conv_lhs => rw [←hsub]
        ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=N)) hscaled

end SymmetricSubgroupAsymptotics.PrimeIndexAbelianClassCount
