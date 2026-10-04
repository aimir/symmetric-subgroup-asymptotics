import SymmetricSubgroupAsymptotics.SocleNormalGeneratorNumber
import Mathlib.GroupTheory.Index

/-!
# Normal generators of a finite socle from factor sizes

This file isolates the group-theoretic core of the finite affine character
route.  A finite family of minimal normal subgroups can be pruned greedily:
whenever a new member is not already in the accumulated product, its
intersection with that product is trivial.  Its order therefore multiplies
the accumulated order.  Choosing one nonidentity element from every retained
member normally generates their supremum.

Consequently, if every minimal normal subgroup has order at least `m` and the
socle has order at most `m^t`, the socle needs at most `t` normal generators.
Together with `SocleNormalGeneratorNumber`, this produces the exact tuple
consumed by the published Zmud theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem finset_sup_normal {G : Type} [Group G]
    (A : Finset (Subgroup G))
    (hA : ∀ N ∈ A, N.Normal) :
    (A.sup (fun N : Subgroup G => N)).Normal := by
  induction A using Finset.induction_on with
  | empty =>
      simp
  | @insert N A hN ih =>
      letI : N.Normal := hA N (Finset.mem_insert_self N A)
      letI : (A.sup (fun M : Subgroup G => M)).Normal := ih (fun M hM =>
        hA M (Finset.mem_insert_of_mem hM))
      simpa only [Finset.sup_insert, id_eq] using
        (inferInstance : (N ⊔ A.sup (fun M : Subgroup G => M)).Normal)

private theorem card_sup_eq_mul_of_minimal_not_le
    {G : Type} [Group G] [Finite G]
    (N P : Subgroup G) (hN : IsMinimalNormalSubgroup N)
    [P.Normal] (hnot : ¬ N ≤ P) :
    Nat.card ↥(N ⊔ P) = Nat.card N * Nat.card P := by
  letI : N.Normal := hN.1
  have hinf : N ⊓ P = ⊥ := by
    by_contra hne
    have hnormal : (N ⊓ P).Normal := inferInstance
    have heq : N ⊓ P = N := hN.2.2 (N ⊓ P) hnormal hne inf_le_left
    exact hnot (by rw [← heq]; exact inf_le_right)
  have hle : N ≤ N ⊔ P := le_sup_left
  have hcard := (N.subgroupOf (N ⊔ P)).card_mul_index
  have hsubcard : Nat.card (N.subgroupOf (N ⊔ P)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have hindex : (N.subgroupOf (N ⊔ P)).index = Nat.card P := by
    change N.relIndex (N ⊔ P) = Nat.card P
    rw [Subgroup.relIndex_sup_left, ← Subgroup.inf_relIndex_right, hinf,
      Subgroup.relIndex_bot_left]
  rw [hsubcard, hindex] at hcard
  exact hcard.symm

private theorem exists_independent_minimal_subfamily
    {G : Type} [Group G] [Finite G]
    (A : Finset (Subgroup G))
    (hA : ∀ N ∈ A, IsMinimalNormalSubgroup N)
    (m : ℕ) (hcard : ∀ N ∈ A, m ≤ Nat.card N) :
    ∃ B : Finset (Subgroup G),
      B ⊆ A ∧
        B.sup (fun N : Subgroup G => N) =
          A.sup (fun N : Subgroup G => N) ∧
        m ^ B.card ≤ Nat.card ↥(B.sup (fun N : Subgroup G => N)) := by
  induction A using Finset.induction_on with
  | empty =>
      refine ⟨∅, Finset.Subset.rfl, rfl, ?_⟩
      simp
  | @insert N A hNA ih =>
      have hA' : ∀ M ∈ A, IsMinimalNormalSubgroup M := fun M hM =>
        hA M (Finset.mem_insert_of_mem hM)
      obtain ⟨B, hBA, hsup, hpow⟩ := ih hA'
        (fun M hM => hcard M (Finset.mem_insert_of_mem hM))
      by_cases hle : N ≤ B.sup (fun M : Subgroup G => M)
      · refine ⟨B, fun M hM => Finset.mem_insert_of_mem (hBA hM), ?_, hpow⟩
        rw [Finset.sup_insert, ← hsup]
        exact (sup_eq_right.mpr hle).symm
      · have hNB : N ∉ B := by
          intro hmem
          exact hle (Finset.le_sup (f := id) hmem)
        letI : (B.sup (fun M : Subgroup G => M)).Normal :=
          finset_sup_normal B (fun M hM =>
          (hA' M (hBA hM)).1)
        have hmul : Nat.card ↥(N ⊔ B.sup (fun M : Subgroup G => M)) =
            Nat.card N * Nat.card ↥(B.sup (fun M : Subgroup G => M)) :=
          card_sup_eq_mul_of_minimal_not_le N
            (B.sup (fun M : Subgroup G => M))
            (hA N (Finset.mem_insert_self N A)) hle
        refine ⟨insert N B, ?_, ?_, ?_⟩
        · intro M hM
          rcases Finset.mem_insert.mp hM with rfl | hM
          · exact Finset.mem_insert_self _ A
          · exact Finset.mem_insert_of_mem (hBA hM)
        · rw [Finset.sup_insert, Finset.sup_insert, ← hsup]
        · rw [Finset.card_insert_of_notMem hNB, pow_succ, Finset.sup_insert,
            hmul]
          simpa only [Nat.mul_comm] using
            Nat.mul_le_mul hpow (hcard N (Finset.mem_insert_self N A))

private theorem normalGen_finset_sup_minimal_le_card
    {G : Type} [Group G] [Finite G]
    (B : Finset (Subgroup G))
    (hB : ∀ N ∈ B, IsMinimalNormalSubgroup N) :
    MarkedC4.normalGen (B.sup (fun N : Subgroup G => N)) ≤ B.card := by
  letI : (B.sup (fun N : Subgroup G => N)).Normal :=
    finset_sup_normal B (fun N hN => (hB N hN).1)
  let pick : Subgroup G → G := fun N =>
    if h : IsMinimalNormalSubgroup N then
      (Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp h.2.1) : N).1
    else 1
  have pick_mem (N : Subgroup G) (hN : IsMinimalNormalSubgroup N) :
      pick N ∈ N := by
    simp only [pick, dif_pos hN]
    exact (Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp hN.2.1)).2
  have pick_ne (N : Subgroup G) (hN : IsMinimalNormalSubgroup N) :
      pick N ≠ 1 := by
    simp only [pick, dif_pos hN]
    exact_mod_cast
      (Classical.choose_spec (Subgroup.ne_bot_iff_exists_ne_one.mp hN.2.1))
  let T : Finset G := B.image pick
  have hTsub : (T : Set G) ⊆
      ((B.sup (fun N : Subgroup G => N) : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨N, hNB, rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.le_sup (f := fun M : Subgroup G => M) hNB)
      (pick_mem N (hB N hNB))
  have hclosure : Subgroup.normalClosure (T : Set G) =
      B.sup (fun N : Subgroup G => N) := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal hTsub
    · apply Finset.sup_le
      intro N hNB
      letI : N.Normal := (hB N hNB).1
      let M := N ⊓ Subgroup.normalClosure (T : Set G)
      have hMnormal : M.Normal := inferInstance
      have hMne : M ≠ ⊥ := by
        rw [Subgroup.ne_bot_iff_exists_ne_one]
        let y : M := ⟨pick N, pick_mem N (hB N hNB),
          Subgroup.subset_normalClosure (by
            exact Finset.mem_image.mpr ⟨N, hNB, rfl⟩)⟩
        exact ⟨y, by
          intro hy
          exact pick_ne N (hB N hNB) (congrArg Subtype.val hy)⟩
      have hMN : M = N := (hB N hNB).2.2 M hMnormal hMne inf_le_left
      intro x hx
      have : x ∈ M := by rw [hMN]; exact hx
      exact this.2
  calc
    MarkedC4.normalGen (B.sup (fun N : Subgroup G => N)) ≤ T.card :=
      MarkedC4.normalGen_le hTsub hclosure
    _ ≤ B.card := Finset.card_image_le

/-- The part of the ambient socle carried by a fixed subgroup.  The factors
in this definition are minimal normal subgroups of the ambient group, not
minimal normal subgroups of `K` considered as an abstract group.  This
distinction is essential for affine translation sections: an elementary
abelian section has many intrinsic order-`p` minimal subgroups, while its
ambient irreducible factors can all have order at least `p^d`. -/
def finiteGroupSoclePart
    (G : Type) [Group G] [Finite G] (K : Subgroup G) : Subgroup G :=
  (Finset.univ.filter fun N : Subgroup G =>
    IsMinimalNormalSubgroup N ∧ N ≤ K).sup id

instance finiteGroupSoclePart_normal
    (G : Type) [Group G] [Finite G] (K : Subgroup G) :
    (finiteGroupSoclePart G K).Normal := by
  apply finset_sup_normal
  intro N hN
  exact (Finset.mem_filter.mp hN).2.1.1

/-- Every ambient minimal factor selected by `finiteGroupSoclePart` lies in
the prescribed carrier. -/
theorem finiteGroupSoclePart_le
    (G : Type) [Group G] [Finite G] (K : Subgroup G) :
    finiteGroupSoclePart G K ≤ K := by
  apply Finset.sup_le
  intro N hN
  exact (Finset.mem_filter.mp hN).2.2

/-- The selected part lies in the full ambient socle. -/
theorem finiteGroupSoclePart_le_socle
    (G : Type) [Group G] [Finite G] (K : Subgroup G) :
    finiteGroupSoclePart G K ≤ finiteGroupSocle G := by
  apply Finset.sup_le
  intro N hN x hx
  exact Subgroup.subset_normalClosure
    ⟨N, (Finset.mem_filter.mp hN).2.1, hx⟩

/-- Ambient-factor version of the finite cardinal argument.  If every
minimal normal factor of `G` lying in `K` has order at least `m`, and `K`
has order at most `m^t`, then the sum of precisely those ambient factors
needs at most `t` normal generators in `G`.

No assertion is made about the intrinsic minimal normal subgroups of `K`. -/
theorem normalGen_finiteGroupSoclePart_le_of_card
    (G : Type) [Group G] [Finite G]
    (K : Subgroup G) (m t : ℕ) (hm : 2 ≤ m)
    (hmin : ∀ N : Subgroup G, IsMinimalNormalSubgroup N → N ≤ K →
      m ≤ Nat.card N)
    (hK : Nat.card K ≤ m ^ t) :
    MarkedC4.normalGen (finiteGroupSoclePart G K) ≤ t := by
  let A : Finset (Subgroup G) := Finset.univ.filter fun N : Subgroup G =>
    IsMinimalNormalSubgroup N ∧ N ≤ K
  have hA : ∀ N ∈ A, IsMinimalNormalSubgroup N := by
    intro N hN
    exact (Finset.mem_filter.mp hN).2.1
  obtain ⟨B, hBA, hBsup, hpow⟩ :=
    exists_independent_minimal_subfamily A hA m
      (fun N hN => hmin N (hA N hN)
        (Finset.mem_filter.mp hN).2.2)
  have hB : ∀ N ∈ B, IsMinimalNormalSubgroup N := fun N hN =>
    hA N (hBA hN)
  have hB_le_K : B.sup (fun N : Subgroup G => N) ≤ K := by
    apply Finset.sup_le
    intro N hN
    exact (Finset.mem_filter.mp (hBA hN)).2.2
  have hpow' : m ^ B.card ≤ m ^ t := by
    calc
      m ^ B.card ≤ Nat.card ↥(B.sup (fun N : Subgroup G => N)) := hpow
      _ ≤ Nat.card K := Subgroup.card_le_of_le hB_le_K
      _ ≤ m ^ t := hK
  have hcardBt : B.card ≤ t :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < m)).mp hpow'
  change MarkedC4.normalGen (A.sup id) ≤ t
  have hsup_id : A.sup id = B.sup id := by
    simpa only using hBsup.symm
  rw [hsup_id]
  exact (normalGen_finset_sup_minimal_le_card B hB).trans hcardBt

/-- Exact padded-tuple form of the ambient-factor cardinal theorem. -/
theorem exists_normal_generating_tuple_finiteGroupSoclePart_of_card
    (G : Type) [Group G] [Finite G]
    (K : Subgroup G) (m t : ℕ) (hm : 2 ≤ m)
    (hmin : ∀ N : Subgroup G, IsMinimalNormalSubgroup N → N ≤ K →
      m ≤ Nat.card N)
    (hK : Nat.card K ≤ m ^ t) :
    ∃ x : Fin t → G,
      Subgroup.normalClosure (Set.range x) = finiteGroupSoclePart G K :=
  exists_normal_generating_tuple_of_normalGen_le
    (finiteGroupSoclePart G K)
    (normalGen_finiteGroupSoclePart_le_of_card G K m t hm hmin hK)

/-- If every minimal normal subgroup has order at least `m` and the whole
socle has order at most `m^t`, then `t` elements normally generate it. -/
theorem normalGen_finiteGroupSocle_le_of_card
    (G : Type) [Group G] [Finite G]
    (m t : ℕ) (hm : 2 ≤ m)
    (hmin : ∀ N : Subgroup G, IsMinimalNormalSubgroup N →
      m ≤ Nat.card N)
    (hsoc : Nat.card (finiteGroupSocle G) ≤ m ^ t) :
    MarkedC4.normalGen (finiteGroupSocle G) ≤ t := by
  let A : Finset (Subgroup G) := Finset.univ.filter IsMinimalNormalSubgroup
  have hA : ∀ N ∈ A, IsMinimalNormalSubgroup N := by
    intro N hN
    exact (Finset.mem_filter.mp hN).2
  have hsup : A.sup (fun N : Subgroup G => N) = finiteGroupSocle G := by
    letI : (A.sup (fun N : Subgroup G => N)).Normal :=
      finset_sup_normal A (fun N hN => (hA N hN).1)
    apply le_antisymm
    · apply Finset.sup_le
      intro N hN x hx
      exact Subgroup.subset_normalClosure ⟨N, hA N hN, hx⟩
    · apply Subgroup.normalClosure_le_normal
      rintro x ⟨N, hN, hx⟩
      exact Finset.le_sup (f := id)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ N, hN⟩) hx
  obtain ⟨B, hBA, hBsup, hpow⟩ :=
    exists_independent_minimal_subfamily A hA m
      (fun N hN => hmin N (hA N hN))
  have hB : ∀ N ∈ B, IsMinimalNormalSubgroup N := fun N hN =>
    hA N (hBA hN)
  have hpow' : m ^ B.card ≤ m ^ t := by
    calc
      m ^ B.card ≤ Nat.card ↥(B.sup (fun N : Subgroup G => N)) := hpow
      _ = Nat.card (finiteGroupSocle G) := by rw [hBsup, hsup]
      _ ≤ m ^ t := hsoc
  have hcardBt : B.card ≤ t :=
    (Nat.pow_le_pow_iff_right (by omega : 1 < m)).mp hpow'
  rw [← hsup, ← hBsup]
  exact (normalGen_finset_sup_minimal_le_card B hB).trans hcardBt

/-- Tuple form of `normalGen_finiteGroupSocle_le_of_card`. -/
theorem socleNormalGeneratorBound_of_card
    (G : Type) [Group G] [Finite G]
    (m t : ℕ) (hm : 2 ≤ m)
    (hmin : ∀ N : Subgroup G, IsMinimalNormalSubgroup N →
      m ≤ Nat.card N)
    (hsoc : Nat.card (finiteGroupSocle G) ≤ m ^ t) :
    SocleNormalGeneratorBound G t :=
  (socleNormalGeneratorBound_iff_normalGen_le G t).2
    (normalGen_finiteGroupSocle_le_of_card G m t hm hmin hsoc)

end SymmetricSubgroupAsymptotics

end
