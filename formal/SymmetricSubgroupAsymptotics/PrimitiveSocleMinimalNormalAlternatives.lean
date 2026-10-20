import SymmetricSubgroupAsymptotics.PrimitiveSocleCentralizerRegular

/-! The full primitive socle consists of one selected nonabelian minimal
normal subgroup, or of it and its commuting regular centralizer. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

variable {G : Type} [Group G]

/-- Distinct actual minimal normal subgroups have trivial intersection. -/
theorem minimalNormals_disjoint (E M : Subgroup G)
    (hE : IsMinimalNormalSubgroup E) (hM : IsMinimalNormalSubgroup M) (hne : E≠M) :
    Disjoint E M := by
  letI : E.Normal := hE.1
  letI : M.Normal := hM.1
  apply disjoint_iff.mpr
  by_contra hbot
  have he : E⊓M=E := hE.2.2 (E⊓M) inferInstance hbot inf_le_left
  have hle : E≤M := by rw [←he]; exact inf_le_right
  exact hne (hM.2.2 E inferInstance hE.2.1 hle)

/-- Every other minimal normal is in the actual ambient centralizer. -/
theorem minimalNormal_le_centralizer (E M : Subgroup G)
    (hE : IsMinimalNormalSubgroup E) (hM : IsMinimalNormalSubgroup M) (hne : E≠M) :
    M ≤ Subgroup.centralizer (E : Set G) := by
  intro m hm
  apply Subgroup.mem_centralizer_iff.mpr
  intro e he
  exact (Subgroup.commute_of_normal_of_disjoint E M hE.1 hM.1
    (minimalNormals_disjoint E M hE hM hne) e m he hm).eq

/-- In the trivial-centralizer case, no other actual minimal normal can
contribute to the full socle. -/
theorem full_socle_eq_of_centralizer_bot (E : Subgroup G)
    (hE : IsMinimalNormalSubgroup E)
    (hc : Subgroup.centralizer (E : Set G)=⊥) : finiteGroupSocle G=E := by
  letI : E.Normal := hE.1
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x ⟨M,hM,hx⟩
    by_cases hm : E=M
    · simpa only [←hm] using hx
    · have hle := minimalNormal_le_centralizer E M hE hM hm
      rw [hc] at hle
      exact False.elim (hM.2.1 (le_antisymm hle bot_le))
  · intro e he
    exact Subgroup.subset_normalClosure ⟨E,hE,he⟩

variable {X : Type} [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPreprimitive G X] [Nonempty X]

/-- The nontrivial centralizer is itself a regular minimal normal, and both
regular factors together are exactly the FULL socle. -/
theorem centralizer_regular_alternative (E : Subgroup G)
    (hE : IsMinimalNormalSubgroup E) (hnc : ¬ IsMulCommutative E)
    (hc : Subgroup.centralizer (E : Set G)≠⊥) :
    let C := Subgroup.centralizer (E : Set G)
    IsMinimalNormalSubgroup C ∧ Disjoint E C ∧ finiteGroupSocle G=E⊔C ∧
      (∀ x y : X, ∃! e : E, e • x=y) ∧
      (∀ x y : X, ∃! c : C, c • x=y) := by
  letI : E.Normal := hE.1
  let C : Subgroup G := Subgroup.centralizer (E : Set G)
  letI : MulAction.IsPretransitive E X := normal_transitive_of_ne_bot E hE.2.1
  letI : MulAction.IsPretransitive C X := normal_transitive_of_ne_bot C hc
  have hcomm : ∀ e : E, ∀ c : C, Commute (e : G) (c : G) := by
    intro e c
    exact Subgroup.mem_centralizer_iff.mp c.property (e : G) e.property
  have hregularE : ∀ x y : X, ∃! e : E, e • x=y :=
    regular_of_free E (free_of_commuting_transitive E C hcomm)
  have hregularC : ∀ x y : X, ∃! c : C, c • x=y :=
    regular_of_free C (centralizer_free E)
  have hC : IsMinimalNormalSubgroup C := regular_normal_minimal C hc hregularC
  have hne : E≠C := by
    intro he
    apply hnc
    apply isMulCommutative_iff.mpr
    intro a b
    apply Subtype.ext
    have hb : (b : G)∈C := by rw [←he]; exact b.property
    exact Subgroup.mem_centralizer_iff.mp hb (a : G) a.property
  have hsocle : finiteGroupSocle G=E⊔C := by
    apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      rintro x ⟨M,hM,hx⟩
      by_cases hm : E=M
      · exact Subgroup.mem_sup_left (by simpa only [←hm] using hx)
      · exact Subgroup.mem_sup_right (minimalNormal_le_centralizer E M hE hM hm hx)
    · apply sup_le
      · intro e he
        exact Subgroup.subset_normalClosure ⟨E,hE,he⟩
      · intro c hc
        exact Subgroup.subset_normalClosure ⟨C,hC,hc⟩
  exact ⟨hC,minimalNormals_disjoint E C hE hC hne,hsocle,hregularE,hregularC⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
