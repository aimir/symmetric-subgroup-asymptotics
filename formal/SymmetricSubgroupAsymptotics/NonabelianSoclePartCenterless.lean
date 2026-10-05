import SymmetricSubgroupAsymptotics.MinimalNormalCompositionCharts
import SymmetricSubgroupAsymptotics.NormalGeneratorTypeSharing

/-!
# Nonabelian ambient socle parts are centerless

A sum of nonabelian ambient minimal normal subgroups is centerless.  The
point is ambient minimality: a new factor is either already in the preceding
sum or meets it trivially, and two disjoint normal subgroups commute.  Thus
the nonredundant steps are internal direct products of centerless groups.

Consequently such a selected socle part is disjoint from every commutative
ambient normal subgroup.  This is the structural bridge used by the finite
affine lanes to inject the nonabelian residual socle through the literal top
section, without a catalogue or a new input record.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private theorem finset_sup_normal
    {G : Type} [Group G]
    (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, M.Normal) :
    (S.sup (fun M : Subgroup G => M) : Subgroup G).Normal := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert M S hMS ih =>
      letI : M.Normal := hS M (Finset.mem_insert_self M S)
      letI : (S.sup (fun K : Subgroup G => K) : Subgroup G).Normal :=
        ih (fun K hK => hS K (Finset.mem_insert_of_mem hK))
      simpa only [Finset.sup_insert] using
        (inferInstance :
          (M ⊔ S.sup (fun K : Subgroup G => K)).Normal)

/-- A finite product of centerless groups is centerless. -/
theorem isCenterless_pi
    {ι : Type} [Fintype ι]
    (S : ι → Type) [∀ i, Group (S i)]
    (hS : ∀ i, IsCenterless (S i)) :
    IsCenterless ((i : ι) → S i) := by
  intro x hx
  funext i
  apply hS i (x i)
  intro y
  have h := congrFun (hx (Pi.mulSingle i y)) i
  simpa using h

/-- Centerlessness transports backwards through a multiplicative
 equivalence. -/
theorem isCenterless_of_mulEquiv
    {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (hB : IsCenterless B) : IsCenterless A := by
  intro x hx
  apply e.injective
  rw [map_one]
  apply hB (e x)
  intro z
  obtain ⟨y, rfl⟩ := e.surjective z
  simpa only [map_mul] using congrArg e (hx y)

/-- Every nonabelian ambient minimal normal subgroup is centerless. -/
theorem isCenterless_of_nonabelian_minimalNormal
    {G : Type} [Group G] [Finite G]
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hnonabelian : ¬ IsMulCommutative M) : IsCenterless M := by
  letI : M.Normal := hM.1
  let C : SemisimpleNormalChart M :=
    semisimpleNormalChart_of_nonabelian_minimal M (by
      intro K hK hKM
      by_cases hbot : K = ⊥
      · exact Or.inl hbot
      · exact Or.inr (hM.2.2 K hK hbot hKM)) hnonabelian
  exact isCenterless_of_mulEquiv C.equiv
    (isCenterless_pi C.factor C.centerless)

/-- A direct product step inside one ambient group preserves
centerlessness. -/
theorem isCenterless_sup_of_normal_disjoint
    {G : Type} [Group G]
    (A B : Subgroup G) [A.Normal] [B.Normal]
    (hdis : Disjoint A B)
    (hA : IsCenterless A) (hB : IsCenterless B) :
    IsCenterless ↥(A ⊔ B) := by
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := A) (t := B)).mp x.2
  have hcommAB : ∀ u ∈ A, ∀ v ∈ B, Commute u v := by
    intro u hu v hv
    exact Subgroup.commute_of_normal_of_disjoint A B inferInstance
      inferInstance hdis u v hu hv
  have haCentral : ∀ y : A, (⟨a, ha⟩ : A) * y = y * ⟨a, ha⟩ := by
    intro y
    apply Subtype.ext
    apply mul_right_cancel (b := b)
    have hxy := congrArg Subtype.val
      (hx (⟨y.1, Subgroup.mem_sup_left y.2⟩ : ↥(A ⊔ B)))
    change x.1 * y.1 = y.1 * x.1 at hxy
    calc
      a * y.1 * b = a * (y.1 * b) := by rw [mul_assoc]
      _ = a * (b * y.1) := by rw [(hcommAB y.1 y.2 b hb).eq]
      _ = (a * b) * y.1 := by rw [mul_assoc]
      _ = x.1 * y.1 := by rw [hab]
      _ = y.1 * x.1 := hxy
      _ = y.1 * (a * b) := by rw [hab]
      _ = y.1 * a * b := by rw [mul_assoc]
  have hbCentral : ∀ z : B, (⟨b, hb⟩ : B) * z = z * ⟨b, hb⟩ := by
    intro z
    apply Subtype.ext
    apply mul_left_cancel (a := a)
    have hxz := congrArg Subtype.val
      (hx (⟨z.1, Subgroup.mem_sup_right z.2⟩ : ↥(A ⊔ B)))
    change x.1 * z.1 = z.1 * x.1 at hxz
    calc
      a * (b * z.1) = (a * b) * z.1 := by rw [mul_assoc]
      _ = x.1 * z.1 := by rw [hab]
      _ = z.1 * x.1 := hxz
      _ = z.1 * (a * b) := by rw [hab]
      _ = (z.1 * a) * b := by rw [mul_assoc]
      _ = (a * z.1) * b := by rw [(hcommAB a ha z.1 z.2).eq]
      _ = a * (z.1 * b) := by rw [mul_assoc]
  have haOne : a = 1 := congrArg Subtype.val (hA ⟨a, ha⟩ haCentral)
  have hbOne : b = 1 := congrArg Subtype.val (hB ⟨b, hb⟩ hbCentral)
  apply Subtype.ext
  rw [← hab, haOne, hbOne, one_mul]
  rfl

private theorem finset_sup_normal_centerless_nonabelian_minimal
    {G : Type} [Group G] [Finite G]
    (S : Finset (Subgroup G))
    (hS : ∀ M ∈ S, IsMinimalNormalSubgroup M ∧
      ¬ IsMulCommutative M) :
    IsCenterless ↥(S.sup id) := by
  induction S using Finset.induction_on with
  | empty =>
      intro x _
      apply Subtype.ext
      exact Subgroup.mem_bot.mp x.2
  | @insert M S hMS ih =>
      have hM := hS M (Finset.mem_insert_self M S)
      have hrest : ∀ K ∈ S, IsMinimalNormalSubgroup K ∧
          ¬ IsMulCommutative K := by
        intro K hK
        exact hS K (Finset.mem_insert_of_mem hK)
      have hPcenter : IsCenterless ↥(S.sup id) :=
        ih hrest
      letI : M.Normal := hM.1.1
      letI : (S.sup id : Subgroup G).Normal :=
        finset_sup_normal S (fun K hK => (hrest K hK).1.1)
      by_cases hle : M ≤ S.sup id
      · have heq : M ⊔ S.sup id = S.sup id := sup_eq_right.mpr hle
        rw [Finset.sup_insert, show id M = M by rfl, heq]
        exact hPcenter
      · have hdis : Disjoint M (S.sup id) := by
          rw [disjoint_iff]
          by_contra hne
          have heq : M ⊓ S.sup id = M :=
            hM.1.2.2 _ inferInstance hne inf_le_left
          exact hle (by rw [← heq]; exact inf_le_right)
        rw [Finset.sup_insert]
        exact isCenterless_sup_of_normal_disjoint M
          (S.sup id) hdis
          (isCenterless_of_nonabelian_minimalNormal M hM.1 hM.2)
          hPcenter

/-- The sum of every selected nonabelian ambient minimal normal subgroup is
centerless. -/
theorem nonabelianMinimalNormalSoclePart_centerless
    (G : Type) [Group G] [Finite G]
    (R : Subgroup G → Prop) :
    IsCenterless
      ↥(minimalNormalSoclePart G
        (fun M => R M ∧ ¬ IsMulCommutative M)) := by
  let S : Finset (Subgroup G) :=
    Finset.univ.filter (fun M =>
      IsMinimalNormalSubgroup M ∧
        (R M ∧ ¬ IsMulCommutative M))
  have hcenter : IsCenterless ↥(S.sup id) := by
    apply finset_sup_normal_centerless_nonabelian_minimal
    intro M hM
    have hm := (Finset.mem_filter.mp hM).2
    exact ⟨hm.1, hm.2.2⟩
  have hpart : minimalNormalSoclePart G
      (fun M => R M ∧ ¬ IsMulCommutative M) = S.sup id := by
    apply le_antisymm
    · apply minimalNormalSoclePart_le_of
      intro M hM hMR
      exact Finset.le_sup (f := id) (by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ M, hM, hMR⟩)
    · apply Finset.sup_le
      intro M hMS
      have hm := (Finset.mem_filter.mp hMS).2
      exact minimalNormal_le_minimalNormalSoclePart
        (fun K => R K ∧ ¬ IsMulCommutative K) M hm.1 hm.2
  rw [hpart]
  exact hcenter

/-- A selected nonabelian ambient socle part is disjoint from every
commutative ambient normal subgroup. -/
theorem nonabelianMinimalNormalSoclePart_disjoint_commutativeNormal
    {G : Type} [Group G] [Finite G]
    (R : Subgroup G → Prop)
    (D : Subgroup G) [D.Normal] (hD : IsMulCommutative D) :
    Disjoint
      (minimalNormalSoclePart G
        (fun M => R M ∧ ¬ IsMulCommutative M)) D := by
  let H := minimalNormalSoclePart G
    (fun M => R M ∧ ¬ IsMulCommutative M)
  have hHD : H ≤ Subgroup.centralizer (D : Set G) := by
    apply minimalNormalSoclePart_le_of
    intro M hM hMR
    have hnot : ¬ M ≤ D := by
      intro hMD
      apply hMR.2
      exact IsMulCommutative.of_comm fun x y => by
        apply Subtype.ext
        change x.1 * y.1 = y.1 * x.1
        exact congrArg Subtype.val
          (hD.is_comm.comm (⟨x.1, hMD x.2⟩ : D)
            (⟨y.1, hMD y.2⟩ : D))
    have hdis : Disjoint M D := by
      rw [disjoint_iff]
      by_contra hne
      letI : M.Normal := hM.1
      have heq : M ⊓ D = M := hM.2.2 _ inferInstance hne inf_le_left
      exact hnot (by rw [← heq]; exact inf_le_right)
    intro x hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact (Subgroup.commute_of_normal_of_disjoint M D hM.1 inferInstance
      hdis x y hx hy).symm.eq
  rw [Subgroup.disjoint_def]
  intro x hxH hxD
  have hxOne : (⟨x, hxH⟩ : H) = 1 :=
    nonabelianMinimalNormalSoclePart_centerless G R ⟨x, hxH⟩ (by
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp (hHD y.2) x hxD)
  exact congrArg Subtype.val hxOne

/-- Intersection form of the preceding theorem. -/
theorem nonabelianMinimalNormalSoclePart_inf_commutativeNormal_eq_bot
    {G : Type} [Group G] [Finite G]
    (R : Subgroup G → Prop)
    (D : Subgroup G) [D.Normal] (hD : IsMulCommutative D) :
    minimalNormalSoclePart G
        (fun M => R M ∧ ¬ IsMulCommutative M) ⊓ D = ⊥ :=
  (nonabelianMinimalNormalSoclePart_disjoint_commutativeNormal R D hD).eq_bot

/-- A selected sum of nonabelian ambient minimal normal subgroups is
perfect.  Minimality makes the commutator of each selected factor either
trivial or the whole factor, and noncommutativity excludes the first
case. -/
theorem commutator_nonabelianMinimalNormalSoclePart
    (G : Type) [Group G] [Finite G]
    (R : Subgroup G → Prop) :
    ⁅minimalNormalSoclePart G
        (fun M => R M ∧ ¬ IsMulCommutative M),
      minimalNormalSoclePart G
        (fun M => R M ∧ ¬ IsMulCommutative M)⁆ =
      minimalNormalSoclePart G
        (fun M => R M ∧ ¬ IsMulCommutative M) := by
  apply le_antisymm (Subgroup.commutator_le_right _ _)
  apply minimalNormalSoclePart_le_of
  intro M hM hMR
  letI : M.Normal := hM.1
  have hMM : ⁅M, M⁆ = M := by
    apply hM.2.2 ⁅M, M⁆ inferInstance
    · intro hbot
      apply hMR.2
      apply IsMulCommutative.of_comm
      intro x y
      apply Subtype.ext
      have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot x.2
      exact (Subgroup.mem_centralizer_iff.mp hc y.1 y.2).symm
    · exact Subgroup.commutator_le_right M M
  have hMle : M ≤ minimalNormalSoclePart G
      (fun K => R K ∧ ¬ IsMulCommutative K) :=
    minimalNormal_le_minimalNormalSoclePart
      (fun K => R K ∧ ¬ IsMulCommutative K) M hM hMR
  rw [← hMM]
  exact Subgroup.commutator_mono hMle hMle

/-- Every selected commutative minimal-normal sum centralizes the selected
nonabelian sum with the same outer predicate. -/
theorem commutativeMinimalNormalSoclePart_le_centralizer_nonabelian
    (G : Type) [Group G] [Finite G]
    (R : Subgroup G → Prop) :
    minimalNormalSoclePart G
        (fun M => R M ∧ IsMulCommutative M) ≤
      Subgroup.centralizer
        (minimalNormalSoclePart G
          (fun M => R M ∧ ¬ IsMulCommutative M) : Set G) := by
  apply minimalNormalSoclePart_le_of
  intro M hM hMR
  letI : M.Normal := hM.1
  have hdis :=
    nonabelianMinimalNormalSoclePart_disjoint_commutativeNormal
      R M hMR.2
  intro x hx
  apply Subgroup.mem_centralizer_iff.mpr
  intro y hy
  exact (Subgroup.commute_of_normal_of_disjoint
    (minimalNormalSoclePart G
      (fun K => R K ∧ ¬ IsMulCommutative K)) M
    inferInstance hM.1 hdis y x hy hx).eq

/-- The nonabelian and abelian selected socle sums share no nontrivial
ambient normal quotient.  This is the Goursat form needed to pair their
normal-generating tuples coordinatewise. -/
theorem noCommonNormalQuotient_nonabelian_commutativeSocleParts
    (G : Type) [Group G] [Finite G]
    (R : Subgroup G → Prop) :
    NoCommonNormalQuotient
      (minimalNormalSoclePart G
        (fun M => R M ∧ ¬ IsMulCommutative M))
      (minimalNormalSoclePart G
        (fun M => R M ∧ IsMulCommutative M)) := by
  apply noCommonNormalQuotient_of_commutator_full_central
    (minimalNormalSoclePart G
      (fun M => R M ∧ ¬ IsMulCommutative M))
  · exact commutator_nonabelianMinimalNormalSoclePart G R
  · exact commutativeMinimalNormalSoclePart_le_centralizer_nonabelian G R

end SymmetricSubgroupAsymptotics

end
