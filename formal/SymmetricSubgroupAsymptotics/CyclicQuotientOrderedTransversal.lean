import SymmetricSubgroupAsymptotics.PGroupOrderedTransversal

/-! A cyclic quotient gives one actual ordered chain of right cosets,
without any primality or splitting assumption. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G] (H : Subgroup G) [H.Normal]
    [IsCyclic (G⧸H)]

theorem cyclicQuotient_orderedTransversal :
    Nonempty (OrderedCosetData H ⊤ (Fin H.index) (· < ·) (· ≤ ·)) := by
  obtain ⟨z,hz⟩ := IsCyclic.exists_generator (α := G⧸H)
  have horder : orderOf z=H.index :=
    (orderOf_eq_card_of_forall_mem_zpowers hz).trans H.index_eq_card.symm
  obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective H z
  refine ⟨{
    le := le_top
    repr := fun i => x^i.val
    mem := fun _ => Subgroup.mem_top _
    factor := ?_
    unique := ?_
    triangular := ?_ }⟩
  · intro y _
    obtain ⟨i,hi⟩ := (finEquivZPowers (isOfFinOrder_of_finite z)).surjective
      ⟨QuotientGroup.mk' H y,hz _⟩
    have hp : z^i.val=QuotientGroup.mk' H y := congrArg Subtype.val hi
    let j : Fin H.index := ⟨i.val,by simpa only [horder] using i.isLt⟩
    have hh : y*(x^j.val)⁻¹∈H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' H (y*(x^j.val)⁻¹)=1
      rw [map_mul,map_inv,map_pow,hx]
      change QuotientGroup.mk' H y*(z^i.val)⁻¹=1
      rw [hp,mul_inv_cancel]
    exact ⟨y*(x^j.val)⁻¹,hh,j,by group⟩
  · intro i j hij
    have hq := (QuotientGroup.eq_one_iff (x^i.val*(x^j.val)⁻¹)).mpr hij
    change QuotientGroup.mk' H (x^i.val*(x^j.val)⁻¹)=1 at hq
    rw [map_mul,map_inv,map_pow,map_pow,hx,mul_inv_eq_one] at hq
    apply Fin.ext
    exact pow_injOn_Iio_orderOf (by simpa only [horder] using i.isLt)
      (by simpa only [horder] using j.isLt) hq
  · intro a b c hab hbc
    let d : Fin H.index := ⟨a.val+(c.val-b.val),by
      have hc := c.isLt
      change a.val<b.val at hab
      change b.val≤c.val at hbc
      omega⟩
    have hdc : d<c := by
      change a.val+(c.val-b.val)<c.val
      change a.val<b.val at hab
      change b.val≤c.val at hbc
      omega
    have hsplit : x^c.val=x^b.val*x^(c.val-b.val) := by
      rw [←pow_add]
      congr 1
      change b.val≤c.val at hbc
      omega
    refine ⟨1,H.one_mem,d,hdc,?_⟩
    change x^a.val*(x^b.val)⁻¹*x^c.val=1*x^(a.val+(c.val-b.val))
    rw [hsplit,pow_add]
    group

end SymmetricSubgroupAsymptotics
