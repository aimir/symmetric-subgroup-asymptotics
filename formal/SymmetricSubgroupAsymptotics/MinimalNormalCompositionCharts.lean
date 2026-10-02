import SymmetricSubgroupAsymptotics.FixedTargetElementaryLayerEnvelope
import SymmetricSubgroupAsymptotics.MinimalNormalSimpleQuotients
import SymmetricSubgroupAsymptotics.SemisimpleSubdirectChart
import SymmetricSubgroupAsymptotics.AbelianMinimalNormal

/-!
# Counting charts for actual minimal normal subgroups

An abelian minimal normal subgroup is put in its genuine elementary
prime-field coordinates and the quotient conjugation action is constructed.
A nonabelian minimal normal subgroup is charted as a product of centerless
simple groups by the proved subdirect-product theorem.  These are structural
theorems, not inputs to the fixed-target composition induction.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative

namespace SymmetricSubgroupAsymptotics

/-- A perfect simple group is centerless. -/
theorem isCenterless_of_simple_perfect
    (S : Type) [Group S] [IsSimpleGroup S] [Group.IsPerfect S] :
    IsCenterless S := by
  intro x hx
  have hxcenter : x ∈ Subgroup.center S :=
    (Subgroup.mem_center_iff).mpr (fun y => (hx y).symm)
  rcases Subgroup.Normal.eq_bot_or_eq_top
      (H := Subgroup.center S) inferInstance with hbot | htop
  · rw [hbot, Subgroup.mem_bot] at hxcenter
    exact hxcenter
  · have hcomm : IsMulCommutative S :=
      isMulCommutative_iff.mpr (fun a b => by
        have ha : a ∈ Subgroup.center S := by rw [htop]; exact Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp ha b).symm)
    have hcommBot : commutator S = ⊥ := (commutator_eq_bot_iff S).mpr hcomm
    have hbotTop : (⊥ : Subgroup S) = ⊤ :=
      hcommBot.symm.trans Group.IsPerfect.commutator_eq_top
    apply Subgroup.mem_bot.mp
    rw [hbotTop]
    exact Subgroup.mem_top x

/-- Every nonabelian minimal normal subgroup has the literal semisimple
chart required by the outer-fibre theorem.  The coordinates are the actual
ambient conjugates of one simple quotient. -/
theorem semisimpleNormalChart_of_nonabelian_minimal_nonempty
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    (hnc : ¬ IsMulCommutative E) :
    Nonempty (SemisimpleNormalChart E) := by
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨M, hM, hsimple, hperfect, honto, hsep⟩ :=
    nonabelian_minimal_normal_simple_coordinates E hmin hnc
  letI : M.Normal := hM
  letI : IsSimpleGroup (E ⧸ M) := hsimple
  letI : Group.IsPerfect (E ⧸ M) := hperfect
  let C : SemisimpleGroupChart E :=
    (semisimpleGroupChart_of_subdirect
      (fun _ : G => E ⧸ M)
      (fun _ => isCenterless_of_simple_perfect (E ⧸ M)) E
      (fun a => (QuotientGroup.mk' M).comp
        (MulAut.conjNormal (H := E) a).toMonoidHom)
      honto hsep).some
  exact ⟨C.toNormalChart E⟩

/-- Data form of the preceding proved existence theorem. -/
noncomputable def semisimpleNormalChart_of_nonabelian_minimal
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    (hnc : ¬ IsMulCommutative E) :
    SemisimpleNormalChart E :=
  Classical.choice
    (semisimpleNormalChart_of_nonabelian_minimal_nonempty E hmin hnc)

/-- Exact elementary coordinates on an abelian nontrivial minimal normal
subgroup. -/
structure ElementaryMinimalNormalChart
    {G : Type} [Group G] (E : Subgroup G) where
  p : ℕ
  p_prime : p.Prime
  [primeFact : Fact p.Prime]
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module (ZMod p) V]
  [finiteDimensional : FiniteDimensional (ZMod p) V]
  equiv : E ≃* Multiplicative V

attribute [instance]
  ElementaryMinimalNormalChart.primeFact
  ElementaryMinimalNormalChart.addCommGroup
  ElementaryMinimalNormalChart.module
  ElementaryMinimalNormalChart.finiteDimensional

/-- Minimal normality forces one prime to act as the exponent of the whole
abelian layer. -/
theorem elementaryMinimalNormalChart_nonempty
    {G : Type} [Group G] [Finite G]
    (E : Subgroup G) [E.Normal]
    (hne : E ≠ ⊥)
    (hcomm : IsMulCommutative E)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E) :
    Nonempty (ElementaryMinimalNormalChart E) := by
  letI : IsMulCommutative E := hcomm
  letI : Nontrivial E := E.nontrivial_iff_ne_bot.mpr hne
  have hcard : Nat.card E ≠ 1 := (Nat.ne_of_gt Finite.one_lt_card)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  letI : Fact p.Prime := ⟨hp⟩
  rcases abelian_minimal_normal_elementary_or_coprime E p hmin with h | hcoprime
  · obtain ⟨V, hVadd, hVmod, hVfd, ⟨e⟩⟩ := h
    exact ⟨{
      p := p
      p_prime := hp
      primeFact := ⟨hp⟩
      V := V
      addCommGroup := hVadd
      module := hVmod
      finiteDimensional := hVfd
      equiv := e }⟩
  · exact False.elim
      ((hp.coprime_iff_not_dvd.mp hcoprime.symm) hpdvd)

namespace ElementaryMinimalNormalChart

variable {G : Type} [Group G] {E : Subgroup G} [E.Normal]
  (C : ElementaryMinimalNormalChart E)

private theorem equiv_ker :
    C.equiv.toMonoidHom.ker = (⊥ : Subgroup G).subgroupOf E := by
  have hker : C.equiv.toMonoidHom.ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff C.equiv.toMonoidHom).mpr C.equiv.injective
  simpa using hker

/-- The literal quotient action induced by ambient conjugation. -/
def quotientRepresentation : Rep (ZMod C.p) (G ⧸ E) :=
  Rep.of (QuotientGroup.lift E
    (normalSectionRepresentation E (⊥ : Subgroup G)
      C.equiv.toMonoidHom C.equiv.surjective C.equiv_ker)
    (le_trans le_sup_left
      (normalSectionRepresentation_ker E (⊥ : Subgroup G)
        C.equiv.toMonoidHom C.equiv.surjective C.equiv_ker)))

@[simp] theorem quotientRepresentation_apply (g : G) (e : E) :
    C.quotientRepresentation.ρ (QuotientGroup.mk' E g) (C.equiv e).toAdd =
      (C.equiv (MulAut.conjNormal g e)).toAdd := by
  exact normalSectionRepresentation_apply E (⊥ : Subgroup G)
    C.equiv.toMonoidHom C.equiv.surjective C.equiv_ker g e

/-- The quotient map's actual kernel in the elementary coordinates. -/
def quotientKernelEquiv :
    Multiplicative C.V ≃* (QuotientGroup.mk' E).ker :=
  C.equiv.symm.trans
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' E).symm)

@[simp] theorem quotientKernelEquiv_coe (v : Multiplicative C.V) :
    ((C.quotientKernelEquiv v : (QuotientGroup.mk' E).ker) : G) =
      (C.equiv.symm v : E) := rfl

/-- Exact original-kernel chart for the elementary minimal normal layer. -/
def originalKernelChart :
    OriginalKernelModuleChart (QuotientGroup.mk' E)
      C.quotientRepresentation where
  equiv := C.quotientKernelEquiv
  conjugate := by
    intro g v
    obtain ⟨e, he⟩ := C.equiv.surjective (Multiplicative.ofAdd v)
    have hev : (C.equiv e).toAdd = v :=
      congrArg Multiplicative.toAdd he
    change ((C.quotientKernelEquiv
      (Multiplicative.ofAdd
        (C.quotientRepresentation.ρ (QuotientGroup.mk' E g) v)) :
          (QuotientGroup.mk' E).ker) : G) = _
    rw [← hev, C.quotientRepresentation_apply]
    change ((C.quotientKernelEquiv
      (Multiplicative.ofAdd (C.equiv (MulAut.conjNormal g e)).toAdd) :
        (QuotientGroup.mk' E).ker) : G) =
      g * ((C.quotientKernelEquiv
        (Multiplicative.ofAdd (C.equiv e).toAdd) :
          (QuotientGroup.mk' E).ker) : G) * g⁻¹
    rw [C.quotientKernelEquiv_coe, C.quotientKernelEquiv_coe]
    simp only [ofAdd_toAdd, C.equiv.symm_apply_apply]
    rfl

end ElementaryMinimalNormalChart

end SymmetricSubgroupAsymptotics

end
