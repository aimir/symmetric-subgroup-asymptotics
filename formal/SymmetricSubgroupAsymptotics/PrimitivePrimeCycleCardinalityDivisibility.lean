import SymmetricSubgroupAsymptotics.PrimitivePrimeCycleCardinalityBand
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Ring

/-! A prime-cycle ordered-tuple orbit supplies cardinality divisibility,
not only a lower bound. In particular p+1 divides the actual group order
whenever p<n<2p. Only the proved multiple-primitivity criterion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitivePrimeCycleCardinalityDivisibility
open MulAction Equiv.Perm

theorem card_dvd_card_of_pretransitive
    {G Y : Type*} [Group G] [Finite G] [Finite Y] [Nonempty Y]
    [MulAction G Y] [IsPretransitive G Y] : Nat.card Y ∣ Nat.card G := by
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  let e : orbit G y ≃ Y :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x,by rw [orbit_eq_univ]; trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G y)
  rw [Nat.card_prod,Nat.card_congr e] at hc
  exact ⟨Nat.card (stabilizer G y),hc.symm⟩

theorem descFactorial_dvd_card_of_multiple_pretransitive
    {G X : Type*} [Group G] [Finite G] [Fintype X] [MulAction G X]
    (k : ℕ) (hk : k≤Nat.card X) (htrans : IsMultiplyPretransitive G X k) :
    (Nat.card X).descFactorial k ∣ Nat.card G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : IsMultiplyPretransitive G X k := htrans
  letI : Nonempty (Fin k ↪ X) := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin k)≤Fintype.card X by
      simpa only [Fintype.card_fin,Nat.card_eq_fintype_card] using hk)
  have hd := card_dvd_card_of_pretransitive (G:=G) (Y:=Fin k ↪ X)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_embedding_eq,Fintype.card_fin] using hd

theorem descFactorial_dvd_card_of_prime_order
    {X : Type*} [Fintype X] (P : Subgroup (Equiv.Perm X))
    (hP : IsPreprimitive P X) (p : ℕ) (hp : p.Prime)
    (g : Equiv.Perm X) (hg : g∈P) (horder : orderOf g=p)
    (hlarge : p<Nat.card X) (hsmall : Nat.card X<2*p) :
    (Nat.card X).descFactorial (Nat.card X-p+1) ∣ Nat.card P := by
  classical
  have hcycle : g.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by simpa only [horder] using hp)
    (by simpa only [Nat.card_eq_fintype_card,horder] using hsmall)
  have hsupport : g.support.card=p := hcycle.orderOf.symm.trans horder
  have hfixcard : Nat.card (SubMulAction.ofFixingSubgroup P (g.supportᶜ : Set X))=p := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype,←hsupport]
    apply congr_arg
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  haveI : IsPretransitive (fixingSubgroup P (g.supportᶜ : Set X))
      (SubMulAction.ofFixingSubgroup P (g.supportᶜ : Set X)) :=
    Equiv.Perm.isPretransitive_of_isCycle_mem hcycle hg
  have hfixprim : IsPreprimitive (fixingSubgroup P (g.supportᶜ : Set X))
      (SubMulAction.ofFixingSubgroup P (g.supportᶜ : Set X)) :=
    IsPreprimitive.of_prime_card (by simpa only [hfixcard] using hp)
  have hsum : g.support.card+(g.supportᶜ : Set X).ncard=Nat.card X := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_add_ncard_compl (g.support : Set X)
  have hcomp : (g.supportᶜ : Set X).ncard=(Nat.card X-p-1)+1 := by
    rw [hsupport] at hsum
    omega
  have hp2 := hp.two_le
  have hmulti : IsMultiplyPreprimitive P X ((Nat.card X-p-1)+2) :=
    hP.isMultiplyPreprimitive hcomp (by omega) hfixprim
  have heq : (Nat.card X-p-1)+2=Nat.card X-p+1 := by omega
  rw [heq] at hmulti
  letI : IsMultiplyPreprimitive P X (Nat.card X-p+1) := hmulti
  exact descFactorial_dvd_card_of_multiple_pretransitive (Nat.card X-p+1) (by omega) inferInstance

/-- The final two factors of the ordered-tuple orbit are p+1 and p. -/
theorem prime_add_one_dvd_card_of_prime_order
    {X : Type*} [Fintype X] (P : Subgroup (Equiv.Perm X))
    (hP : IsPreprimitive P X) (p : ℕ) (hp : p.Prime)
    (g : Equiv.Perm X) (hg : g∈P) (horder : orderOf g=p)
    (hlarge : p<Nat.card X) (hsmall : Nat.card X<2*p) :
    p+1 ∣ Nat.card P := by
  have hd := descFactorial_dvd_card_of_prime_order P hP p hp g hg horder hlarge hsmall
  have hfactor : p+1 ∣ (Nat.card X).descFactorial (Nat.card X-p+1) := by
    have hlen : Nat.card X-p+1=(Nat.card X-(p+1)+1)+1 := by omega
    rw [hlen,Nat.descFactorial_succ,Nat.descFactorial_succ]
    have hlast : Nat.card X-(Nat.card X-(p+1)+1)=p := by omega
    have hnext : Nat.card X-(Nat.card X-(p+1))=p+1 := by omega
    rw [hlast,hnext]
    refine ⟨p*(Nat.card X).descFactorial (Nat.card X-(p+1)),?_⟩
    ring
  exact hfactor.trans hd

end SymmetricSubgroupAsymptotics.PrimitivePrimeCycleCardinalityDivisibility
