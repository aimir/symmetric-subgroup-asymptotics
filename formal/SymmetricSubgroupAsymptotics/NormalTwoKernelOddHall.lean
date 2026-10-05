import SymmetricSubgroupAsymptotics.CyclicQuotientOddHall
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# An odd Hall subgroup above a normal binary kernel

This is the second, purely finite-group, seam needed in the literal
degree-four application of Tracey's Theorem 4.24(ii)(b).  Suppose that
`E ◁ G` is a `2`-group and that `G/E` has a normal odd subgroup `D`
with cyclic quotient.  The odd Hall subgroup of `(G/E)` containing `D`
is constructed in `CyclicQuotientOddHall`.  Pull it back and apply the
formalized Schur--Zassenhaus theorem to `E`; the resulting complement is
an actual `2`-complement of `G`, and its image still contains `D`.

No Hall-existence or strengthened degree-four statement is assumed here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- A normal binary kernel followed by a normal odd layer and a cyclic
quotient has an actual odd Hall subgroup whose quotient image contains the
odd layer. -/
theorem exists_isTwoComplement_mapping_over_oddLayer
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (hE : ∃ a : ℕ, Nat.card E = 2 ^ a)
    (D : Subgroup (G ⧸ E)) [D.Normal]
    [IsCyclic ((G ⧸ E) ⧸ D)]
    (hDodd : ¬2 ∣ Nat.card D) :
    ∃ P : Subgroup G,
      IsTwoComplement P ∧
        D ≤ P.map (QuotientGroup.mk' E) := by
  let Q := G ⧸ E
  let pi : G →* Q := QuotientGroup.mk' E
  obtain ⟨Pq, hDPq, hPq⟩ :=
    exists_isTwoComplement_containing_of_cyclic_quotient D hDodd
  let T : Subgroup G := Pq.comap pi
  let piT : T →* Pq := {
    toFun := fun t ↦ ⟨pi t.1, t.2⟩
    map_one' := by ext; simp [pi]
    map_mul' := by intro x y; ext; simp [pi] }
  have hpiT : Function.Surjective piT := by
    intro q
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective E q.1
    refine ⟨⟨g, ?_⟩, ?_⟩
    · change pi g ∈ Pq
      simpa only [pi, hg] using q.2
    · apply Subtype.ext
      exact hg
  let K : Subgroup T := piT.ker
  have hKnormal : K.Normal := inferInstance
  letI : K.Normal := hKnormal
  have hKcard : Nat.card K = Nat.card E := by
    let e : E →* K := {
      toFun := fun x ↦ ⟨⟨x.1, by
        change pi x.1 ∈ Pq
        have hx : pi x.1 = 1 := (QuotientGroup.eq_one_iff x.1).mpr x.2
        rw [hx]
        exact Pq.one_mem⟩, by
          apply Subtype.ext
          exact (QuotientGroup.eq_one_iff x.1).mpr x.2⟩
      map_one' := by ext; rfl
      map_mul' := by intro x y; ext; rfl }
    have heinj : Function.Injective e := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun z : K ↦ (z.1.1 : G)) hxy)
    have hesurj : Function.Surjective e := by
      intro k
      refine ⟨⟨k.1.1, ?_⟩, ?_⟩
      · have hkoneQ : pi k.1.1 = 1 := congrArg Subtype.val k.2
        exact (QuotientGroup.eq_one_iff k.1.1).mp hkoneQ
      · apply Subtype.ext
        rfl
    exact Nat.card_congr
      (MulEquiv.ofBijective e ⟨heinj, hesurj⟩).toEquiv.symm
  have hKindex : K.index = Nat.card Pq := by
    change piT.ker.index = Nat.card Pq
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hpiT,
      Subgroup.card_top]
  obtain ⟨a, ha⟩ := hE
  have hcop : Nat.Coprime (Nat.card K) K.index := by
    rw [hKcard, ha, hKindex, hPq]
    exact (Nat.coprime_ordCompl Nat.prime_two
      (Nat.card_pos (α := Q)).ne').pow_left a
  obtain ⟨H, hKH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  let P : Subgroup G := H.map T.subtype
  have hPcard : Nat.card P = Nat.card Pq := by
    calc
      Nat.card P = Nat.card H := by
        exact Nat.card_congr
          (H.equivMapOfInjective T.subtype T.subtype_injective).toEquiv.symm
      _ = K.index := hKH.card_right
      _ = Nat.card Pq := hKindex
  refine ⟨P, ?_, ?_⟩
  · change Nat.card P = ordCompl[2] (Nat.card G)
    rw [hPcard, hPq]
    have hGcard := E.card_eq_card_quotient_mul_card_subgroup
    rw [hGcard, Nat.ordCompl_mul, ha,
      Nat.ordCompl_self_pow Nat.prime_two, mul_one]
  · intro d hd
    have hdPq : d ∈ Pq := hDPq hd
    obtain ⟨t, ht⟩ := hpiT ⟨d, hdPq⟩
    obtain ⟨kh, hkh, _hunique⟩ :=
      (Subgroup.isComplement'_def.mp hKH).existsUnique t
    rcases kh with ⟨k, h⟩
    have hkone : piT k = 1 := k.2
    have himage : piT h = ⟨d, hdPq⟩ := by
      apply Subtype.ext
      have heq := congrArg piT hkh
      have heqval := congrArg Subtype.val heq
      simpa only [map_mul, hkone, one_mul, ht] using heqval
    refine ⟨h.1.1, ?_, ?_⟩
    · exact ⟨h.1, h.2, rfl⟩
    · exact congrArg Subtype.val himage

/-- Chain form of the construction.  This is the form used in the actual
Tracey subgroup: `E ◁ B ◁ G`, the binary kernel `E` has prime-power
order, the quotient `B/E` is odd, and the top quotient `G/B` is cyclic. -/
theorem exists_isTwoComplement_mapping_over_normalLayer
    {G : Type} [Group G] [Finite G]
    (E B : Subgroup G) [E.Normal] [B.Normal]
    (hEB : E ≤ B)
    (hE : ∃ a : ℕ, Nat.card E = 2 ^ a)
    (hBodd : ¬2 ∣ Nat.card (B.map (QuotientGroup.mk' E)))
    [IsCyclic (G ⧸ B)] :
    ∃ P : Subgroup G,
      IsTwoComplement P ∧
        B.map (QuotientGroup.mk' E) ≤
          P.map (QuotientGroup.mk' E) := by
  let D : Subgroup (G ⧸ E) := B.map (QuotientGroup.mk' E)
  let e : ((G ⧸ E) ⧸ D) ≃* (G ⧸ B) :=
    QuotientGroup.quotientQuotientEquivQuotient E B hEB
  letI : IsCyclic ((G ⧸ E) ⧸ D) :=
    (MulEquiv.isCyclic e).mpr inferInstance
  exact exists_isTwoComplement_mapping_over_oddLayer E hE D hBodd

end SymmetricSubgroupAsymptotics

end
