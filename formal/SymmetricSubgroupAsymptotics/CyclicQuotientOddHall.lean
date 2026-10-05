import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow

/-!
# The odd Hall subgroup above a normal odd cyclic quotient kernel

Tracey's Theorem 4.24(ii)(b), in characteristic two, asks for a
`2`-complement in a soluble subgroup.  The subgroup used by the degree-four
affine argument has a more rigid form: it has a normal odd subgroup and a
cyclic quotient.  This file constructs the required odd Hall subgroup
directly, without importing Hall's theorem for arbitrary soluble groups.

The construction is literal.  In the cyclic quotient choose an element of
order equal to the odd part of the quotient order, take its cyclic subgroup,
and pull that subgroup back.  The pulled-back subgroup contains the original
normal odd subgroup and has order exactly the odd part of the ambient group
order.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- In this project, a characteristic-two `p`-complement is recorded by the
literal order condition appearing in Tracey's theorem: its order is the odd
part of the ambient finite group order. -/
def IsTwoComplement {G : Type} [Group G] [Finite G]
    (P : Subgroup G) : Prop :=
  Nat.card P = ordCompl[2] (Nat.card G)

/-- If `D` is a normal odd subgroup and `G/D` is cyclic, the odd part of the
cyclic quotient pulls back to a `2`-complement of `G` containing `D`.

This is the Hall-complement seam needed for the actual degree-four Tracey
subgroup.  It is proved from finite cyclic-group arithmetic rather than
assumed as part of the literature interface. -/
theorem exists_isTwoComplement_containing_of_cyclic_quotient
    {G : Type} [Group G] [Finite G]
    (D : Subgroup G) [D.Normal]
    [IsCyclic (G ⧸ D)]
    (hDodd : ¬2 ∣ Nat.card D) :
    ∃ P : Subgroup G, D ≤ P ∧ IsTwoComplement P := by
  let Q := G ⧸ D
  let d := ordCompl[2] (Nat.card Q)
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hdpos : 0 < d := Nat.ordCompl_pos 2 hQpos.ne'
  have hdvd : d ∣ Nat.card Q := Nat.ordCompl_dvd (Nat.card Q) 2
  letI : Fintype Q := Fintype.ofFinite Q
  have hdvd' : d ∣ Fintype.card Q := by
    simpa only [Nat.card_eq_fintype_card] using hdvd
  have hcount :
      Finset.card (Finset.filter (fun q : Q ↦ orderOf q = d) Finset.univ) =
        Nat.totient d :=
    IsCyclic.card_orderOf_eq_totient hdvd'
  have hsetpos :
      0 < Finset.card
        (Finset.filter (fun q : Q ↦ orderOf q = d) Finset.univ) := by
    rw [hcount]
    exact Nat.totient_pos.mpr hdpos
  obtain ⟨q, hq⟩ := Finset.card_pos.mp hsetpos
  have hqorder : orderOf q = d := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hq
  let Pq : Subgroup Q := Subgroup.zpowers q
  let P : Subgroup G := Pq.comap (QuotientGroup.mk' D)
  refine ⟨P, ?_, ?_⟩
  · intro x hx
    change QuotientGroup.mk' D x ∈ Pq
    have hxone : QuotientGroup.mk' D x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr hx
    rw [hxone]
    exact Pq.one_mem
  · change Nat.card P = ordCompl[2] (Nat.card G)
    have hDcompl : ordCompl[2] (Nat.card D) = Nat.card D :=
      (Nat.ordCompl_eq_self_iff_zero_or_not_dvd
        (Nat.card D) Nat.prime_two).mpr (Or.inr hDodd)
    have hGcard := D.card_eq_card_quotient_mul_card_subgroup
    have hPqcard' : Fintype.card (Subgroup.zpowers q) = d := by
      rw [Fintype.card_zpowers, hqorder]
    have hPqcard : Nat.card Pq = d := by
      simpa only [Pq, Nat.card_eq_fintype_card] using hPqcard'
    have hPqSetCard : Nat.card (Pq : Set Q) = d := by
      simpa only using hPqcard
    change Nat.card
        ((QuotientGroup.mk : G → Q) ⁻¹' (Pq : Set Q)) =
      ordCompl[2] (Nat.card G)
    rw [QuotientGroup.card_preimage_mk, hPqSetCard,
      hGcard, Nat.ordCompl_mul, hDcompl]
    exact Nat.mul_comm _ _

end SymmetricSubgroupAsymptotics

end
