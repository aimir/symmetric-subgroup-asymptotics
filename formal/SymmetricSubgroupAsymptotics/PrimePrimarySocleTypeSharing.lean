import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing
import SymmetricSubgroupAsymptotics.PrimeFrattiniGenerators
import Mathlib.GroupTheory.PGroup

/-!
# Prime-primary socle types share normal-generator slots

Split the ambient minimal normal subgroups according to whether they are
`p`-groups.  The two resulting socle sums have no common nontrivial ambient
normal quotient.

The proof stays inside the original finite group.  If an ambient-normal
subgroup gave a common quotient, that quotient would be a `p`-group because
it is already an image of the prime-primary part.  For a complementary
minimal normal factor `M`, minimality makes the kernel of its map to that
quotient either all of `M` or trivial.  The latter alternative would embed
`M` into a `p`-group, contradicting the defining complementary type.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace MarkedC4

/-- Normal generation inside a normal subgroup is at least as restrictive
as normal generation in the ambient group. -/
theorem normalGen_normalSubgroup_le_internal
    {G : Type} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] :
    normalGen H ≤ normalGen (⊤ : Subgroup H) := by
  obtain ⟨s, hsCard, -, hsClosure⟩ := normalGen_spec (⊤ : Subgroup H)
  let T : Finset G := s.image H.subtype
  have hTH : (T : Set G) ⊆ H := by
    intro x hx
    simp only [T, Finset.coe_image, Set.mem_image] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact y.2
  have hclosure : Subgroup.normalClosure (T : Set G) = H := by
    apply le_antisymm
    · exact Subgroup.normalClosure_le_normal hTH
    · have hmap :
          ((Subgroup.normalClosure (s : Set H)).map H.subtype : Subgroup G) ≤
            Subgroup.normalClosure (T : Set G) := by
        simpa only [T, Finset.coe_image] using
          Subgroup.map_normalClosure_le (s : Set H) H.subtype
      rw [hsClosure, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
      exact hmap
  calc
    normalGen H ≤ T.card := normalGen_le hTH hclosure
    _ ≤ s.card := Finset.card_image_le
    _ = normalGen (⊤ : Subgroup H) := hsCard

/-- An ambient-normal `p`-subgroup costs at most its literal
prime-character rank.  Burnside's basis theorem is applied internally and
the resulting tuple is then viewed in the original ambient group. -/
theorem normalGen_normalSubgroup_le_primeCharacterRank
    (p : ℕ) [Fact p.Prime]
    {G : Type} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (hH : IsPGroup p H) :
    normalGen H ≤ Module.finrank (ZMod p) (PrimeCharacters p H) := by
  apply (normalGen_normalSubgroup_le_internal H).trans
  obtain ⟨g, hg⟩ := exists_primeFrattini_generating_tuple p hH
  apply normalGen_le_of_fin_tuple g
  apply top_unique
  rw [← hg]
  exact Subgroup.closure_le_normalClosure

end MarkedC4

private theorem finset_sup_isPGroup_of_normal
    (p : ℕ) [Fact p.Prime]
    {G : Type} [Group G]
    (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, M.Normal ∧ IsPGroup p M) :
    IsPGroup p ((S.sup (fun M : Subgroup G => M) : Subgroup G)) := by
  induction S using Finset.induction_on with
  | empty => simpa using (IsPGroup.of_bot (p := p) (G := G))
  | @insert M S hMS ih =>
      have hM := hS M (Finset.mem_insert_self M S)
      letI : M.Normal := hM.1
      have hrest : ∀ K ∈ S, K.Normal ∧ IsPGroup p K := by
        intro K hK
        exact hS K (Finset.mem_insert_of_mem hK)
      have hSp : IsPGroup p
          ((S.sup (fun K : Subgroup G => K) : Subgroup G)) := ih hrest
      rw [Finset.sup_insert]
      exact hM.2.to_sup_of_normal_left hSp

/-- The selected sum of ambient minimal normal `p`-subgroups is itself a
`p`-group.  The auxiliary predicate permits the prime split to be iterated
inside a previously selected collection of socle types. -/
theorem primePrimarySoclePart_isPGroup_of_predicate
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G]
    (R : Subgroup G → Prop) :
    IsPGroup p
      (minimalNormalSoclePart G (fun M => R M ∧ IsPGroup p M)) := by
  unfold minimalNormalSoclePart
  apply finset_sup_isPGroup_of_normal p
  intro M hM
  have hm : IsMinimalNormalSubgroup M ∧
      (R M ∧ IsPGroup p M) := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hM
  exact ⟨hm.1.1, hm.2.2⟩

/-- Unrestricted specialization of
`primePrimarySoclePart_isPGroup_of_predicate`. -/
theorem primePrimarySoclePart_isPGroup
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G] :
    IsPGroup p (minimalNormalSoclePart G (fun M => IsPGroup p M)) := by
  have h := primePrimarySoclePart_isPGroup_of_predicate p G (fun _ => True)
  have heq :
      minimalNormalSoclePart G (fun M => True ∧ IsPGroup p M) =
        minimalNormalSoclePart G (fun M => IsPGroup p M) := by
    apply minimalNormalSoclePart_congr
    intro M _
    simp
  rw [← heq]
  exact h

private theorem isPGroup_of_map_into_isPGroup_of_minimal
    (p : ℕ) [Fact p.Prime]
    {G Q : Type} [Group G] [Group Q]
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (f : G →* Q) (himage : IsPGroup p (M.map f))
    (hne : M.map f ≠ ⊥) :
    IsPGroup p M := by
  letI : M.Normal := hM.1
  have hnotker : ¬ M ≤ f.ker := by
    intro h
    exact hne ((Subgroup.map_eq_bot_iff (H := M)).mpr h)
  have hinter_normal : (M ⊓ f.ker).Normal := inferInstance
  have hinter : M ⊓ f.ker = ⊥ := by
    by_contra hnebot
    have htop : M ⊓ f.ker = M :=
      hM.2.2 (M ⊓ f.ker) hinter_normal hnebot inf_le_left
    exact hnotker (by
        intro m hm
        have hm' : m ∈ M ⊓ f.ker := by
          rw [htop]
          exact hm
        exact hm'.2)
  let fm : M →* M.map f := f.subgroupMap M
  have hfm_injective : Function.Injective fm := by
    intro x y hxy
    apply Subtype.ext
    apply mul_inv_eq_one.mp
    have hker : (x.1 * y.1⁻¹) ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mpr (congrArg Subtype.val hxy)
    have hinf : x.1 * y.1⁻¹ ∈ M ⊓ f.ker :=
      ⟨M.mul_mem x.2 (M.inv_mem y.2), hker⟩
    rw [hinter] at hinf
    exact Subgroup.mem_bot.mp hinf
  exact himage.of_injective fm hfm_injective

/-- Prime-primary and complementary ambient minimal-normal types have no
common nontrivial ambient normal quotient. -/
theorem noCommonNormalQuotient_primePrimarySocleParts
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G] :
    NoCommonNormalQuotient
      (minimalNormalSoclePart G (fun M => IsPGroup p M))
      (minimalNormalSoclePart G (fun M => ¬ IsPGroup p M)) := by
  let A := minimalNormalSoclePart G (fun M => IsPGroup p M)
  let B := minimalNormalSoclePart G (fun M => ¬ IsPGroup p M)
  intro H hH hHS hHA hHB
  letI : H.Normal := hH
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have hmapH : H.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (H := H)).mpr
    simpa only [q, QuotientGroup.ker_mk'] using (le_refl H)
  have hmapS_A : (A ⊔ B).map q = A.map q := by
    rw [← hHA, Subgroup.map_sup, hmapH, bot_sup_eq]
  have hpA : IsPGroup p A := by
    simpa only [A] using primePrimarySoclePart_isPGroup p G
  have hpS : IsPGroup p ((A ⊔ B).map q) := by
    rw [hmapS_A]
    exact hpA.map q
  have hBker : B ≤ q.ker := by
    apply minimalNormalSoclePart_le_of
    intro M hMmin hMnot
    have hMS : M ≤ A ⊔
        minimalNormalSoclePart G (fun K => ¬ IsPGroup p K) := by
      exact (minimalNormal_le_minimalNormalSoclePart
        (fun K : Subgroup G => ¬ IsPGroup p K) M hMmin hMnot).trans
          le_sup_right
    have hpImage : IsPGroup p (M.map q) :=
      hpS.to_le (Subgroup.map_mono hMS)
    by_contra hnot
    have hne : M.map q ≠ ⊥ := by
      intro hbot
      exact hnot ((Subgroup.map_eq_bot_iff (H := M)).mp hbot)
    exact hMnot (isPGroup_of_map_into_isPGroup_of_minimal
      p M hMmin q hpImage hne)
  have hBH : B ≤ H := by
    simpa only [q, QuotientGroup.ker_mk'] using hBker
  have hsup : H ⊔ B = H := sup_eq_left.mpr hBH
  exact hsup.symm.trans hHB

/-- The two prime types therefore share one padded normal-generator tuple. -/
theorem normalGen_finiteGroupSocle_le_max_primePrimaryParts
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G] :
    MarkedC4.normalGen (finiteGroupSocle G) ≤
      max
        (MarkedC4.normalGen
          (minimalNormalSoclePart G (fun M => IsPGroup p M)))
        (MarkedC4.normalGen
          (minimalNormalSoclePart G (fun M => ¬ IsPGroup p M))) :=
  normalGen_finiteGroupSocle_le_max_of_noCommonNormalQuotient G
    (fun M => IsPGroup p M)
    (noCommonNormalQuotient_primePrimarySocleParts p G)

/-! ## The same split inside a selected socle family -/

/-- Splitting a selected family of ambient minimal normal subgroups into
its `p`-primary and non-`p`-primary members recovers the original selected
socle sum. -/
theorem primePrimarySocleParts_sup_of_predicate
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G]
    (R : Subgroup G → Prop) :
    minimalNormalSoclePart G (fun M => R M ∧ IsPGroup p M) ⊔
        minimalNormalSoclePart G (fun M => R M ∧ ¬ IsPGroup p M) =
      minimalNormalSoclePart G R := by
  apply le_antisymm
  · apply sup_le
    · apply minimalNormalSoclePart_le_of
      intro M hMmin hMR
      exact minimalNormal_le_minimalNormalSoclePart R M hMmin hMR.1
    · apply minimalNormalSoclePart_le_of
      intro M hMmin hMR
      exact minimalNormal_le_minimalNormalSoclePart R M hMmin hMR.1
  · apply minimalNormalSoclePart_le_of
    intro M hMmin hMR
    by_cases hp : IsPGroup p M
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K : Subgroup G => R K ∧ IsPGroup p K)
          M hMmin ⟨hMR, hp⟩).trans le_sup_left
    · exact (minimalNormal_le_minimalNormalSoclePart
          (fun K : Subgroup G => R K ∧ ¬ IsPGroup p K)
          M hMmin ⟨hMR, hp⟩).trans le_sup_right

/-- Inside any selected socle family, its prime-primary and complementary
types have no common nontrivial ambient normal quotient. -/
theorem noCommonNormalQuotient_primePrimarySocleParts_of_predicate
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G]
    (R : Subgroup G → Prop) :
    NoCommonNormalQuotient
      (minimalNormalSoclePart G (fun M => R M ∧ IsPGroup p M))
      (minimalNormalSoclePart G (fun M => R M ∧ ¬ IsPGroup p M)) := by
  let A := minimalNormalSoclePart G (fun M => R M ∧ IsPGroup p M)
  let B := minimalNormalSoclePart G (fun M => R M ∧ ¬ IsPGroup p M)
  intro H hH hHS hHA hHB
  letI : H.Normal := hH
  let q : G →* G ⧸ H := QuotientGroup.mk' H
  have hmapH : H.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (H := H)).mpr
    simpa only [q, QuotientGroup.ker_mk'] using (le_refl H)
  have hmapS_A : (A ⊔ B).map q = A.map q := by
    rw [← hHA, Subgroup.map_sup, hmapH, bot_sup_eq]
  have hpA : IsPGroup p A := by
    simpa only [A] using
      primePrimarySoclePart_isPGroup_of_predicate p G R
  have hpS : IsPGroup p ((A ⊔ B).map q) := by
    rw [hmapS_A]
    exact hpA.map q
  have hBker : B ≤ q.ker := by
    apply minimalNormalSoclePart_le_of
    intro M hMmin hMR
    have hMS : M ≤ A ⊔
        minimalNormalSoclePart G
          (fun K => R K ∧ ¬ IsPGroup p K) := by
      exact (minimalNormal_le_minimalNormalSoclePart
        (fun K : Subgroup G => R K ∧ ¬ IsPGroup p K)
        M hMmin hMR).trans le_sup_right
    have hpImage : IsPGroup p (M.map q) :=
      hpS.to_le (Subgroup.map_mono hMS)
    by_contra hnot
    have hne : M.map q ≠ ⊥ := by
      intro hbot
      exact hnot ((Subgroup.map_eq_bot_iff (H := M)).mp hbot)
    exact hMR.2 (isPGroup_of_map_into_isPGroup_of_minimal
      p M hMmin q hpImage hne)
  have hBH : B ≤ H := by
    simpa only [q, QuotientGroup.ker_mk'] using hBker
  have hsup : H ⊔ B = H := sup_eq_left.mpr hBH
  exact hsup.symm.trans hHB

/-- Selected-family generator form of the iterated prime split. -/
theorem normalGen_minimalNormalSoclePart_le_max_primePrimaryParts
    (p : ℕ) [Fact p.Prime]
    (G : Type) [Group G] [Finite G]
    (R : Subgroup G → Prop) :
    MarkedC4.normalGen (minimalNormalSoclePart G R) ≤
      max
        (MarkedC4.normalGen
          (minimalNormalSoclePart G (fun M => R M ∧ IsPGroup p M)))
        (MarkedC4.normalGen
          (minimalNormalSoclePart G (fun M => R M ∧ ¬ IsPGroup p M))) := by
  rw [← primePrimarySocleParts_sup_of_predicate p G R]
  exact normalGen_sup_le_max_of_noCommonNormalQuotient _ _
    (noCommonNormalQuotient_primePrimarySocleParts_of_predicate p G R)

end SymmetricSubgroupAsymptotics

end
