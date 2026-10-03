import SymmetricSubgroupAsymptotics.RefinedElementaryLayerEnvelope

/-!
# Joint elementary-layer envelope over a fixed top axis

The older one-layer envelope first bounded every descended top by the whole
complete quotient weight and only then summed the original normal axes.  That
is harmless for a fixed target, but it loses the affine induced-module
saving: different intersections above the same top axis must be charged as
one fibre, while different top axes must remain inside the single quotient
menu of the top group.

This file performs exactly that regrouping.  The source `J`, the literal
normal subgroup, its invariant intersection, its descended extension and the
top normal axis are retained until the finite fibre sum.  No splitting or
cohomology vanishing is used.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/- `RefinedElementaryLayerEnvelope` transitively imports the binary-menu
normal-axis enumerator.  The complete quotient count itself was defined with
the canonical subtype enumerator, so keep this theorem on that same finite
enumeration.  The two enumerators have the same elements, but mixing their
`Finset.univ`s obscures the literal fixed-top regrouping below. -/
attribute [-instance] originalNormalFintype

private def quotientEquivOfKernelLe {U R : Type*} [Group U] [Group R]
    (f : U →* R) (hf : Function.Surjective f)
    (N : Subgroup U) [N.Normal] (hker : f.ker ≤ N) :
    letI : (N.map f).Normal := Subgroup.Normal.map (show N.Normal from inferInstance) f hf
    U ⧸ N ≃* R ⧸ N.map f := by
  letI : (N.map f).Normal := Subgroup.Normal.map (show N.Normal from inferInstance) f hf
  let q : U →* R ⧸ N.map f := (QuotientGroup.mk' (N.map f)).comp f
  have hq : Function.Surjective q := (QuotientGroup.mk'_surjective _).comp hf
  have hqker : q.ker = N := by
    ext x
    simp only [q, MonoidHom.mem_ker, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨n, hn, hnx⟩
      have hx : n⁻¹ * x ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
      simpa using N.mul_mem hn (hker hx)
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq hqker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)

variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (π : G →* B) (hπ : Function.Surjective π)
variable (A : Rep (ZMod p) B) [Finite A]
variable (E : OriginalKernelModuleChart π A)

/-- The literal top normal axis attached to an original normal subgroup.
Using `(ker π ⊔ N).map π` makes the quotient appearing in the descended
extension definitionally the quotient indexed by this axis. -/
def elementaryLayerTopAxis
    (N : {N : Subgroup G // N.Normal}) :
    {D : Subgroup B // D.Normal} :=
  ⟨(π.ker ⊔ N.1).map π,
    Subgroup.Normal.map (show (π.ker ⊔ N.1).Normal from inferInstance) π hπ⟩

/-- The finite extension factor attached to one original normal axis. -/
def elementaryLayerAxisCoefficient
    (N : {N : Subgroup G // N.Normal}) : ℝ :=
  (Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
    Nat.card (groupCohomology.H1 (E.sectionRepresentation π A N.1))

theorem elementaryLayerAxisCoefficient_nonneg
    (N : {N : Subgroup G // N.Normal}) :
    0 ≤ elementaryLayerAxisCoefficient p π A E N := by
  unfold elementaryLayerAxisCoefficient
  positivity

/-- A joint capacity package.  `capacity` controls the source-dependent
Schur exponent on every literal section.  `coefficient` controls, uniformly
in the retained top axis, the *sum* of the finite section/H¹ factors over
all original normal subgroups above that axis. -/
structure ElementaryLayerJointCapacityBound where
  capacity : ℝ
  capacity_nonneg : 0 ≤ capacity
  section_capacity : ∀ N : {N : Subgroup G // N.Normal},
    representationSchurCapacity
      (E.sectionRepresentation π A N.1).ρ ≤ capacity
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  fixed_top_fibre : ∀ D : {D : Subgroup B // D.Normal},
    (∑ N : {N : {N : Subgroup G // N.Normal} //
        elementaryLayerTopAxis π hπ N = D},
      elementaryLayerAxisCoefficient p π A E N.1) ≤ coefficient

namespace ElementaryLayerJointCapacityBound

include hπ

/-- Compatibility constructor from the older section-capacity package.
It retains the fixed top literally, but uses the complete finite axis sum as
a uniform fibre bound.  Affine applications replace this coarse coefficient
by the sharper induced-module fibre estimate; the constructor is useful for
all already established elementary rows and for regression checks of the
joint regrouping. -/
noncomputable def ofSectionBound
    (H : ElementaryLayerSectionCapacityBound p π A E) :
    ElementaryLayerJointCapacityBound p π hπ A E where
  capacity := H.capacity
  capacity_nonneg := H.capacity_nonneg
  section_capacity := H.section_capacity
  coefficient := elementaryLayerEnvelopeConstant p π A E
  coefficient_nonneg := by
    unfold elementaryLayerEnvelopeConstant
    exact Finset.sum_nonneg (fun N _ => by
      exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  fixed_top_fibre := by
    intro D
    unfold elementaryLayerEnvelopeConstant
    let P : {N : Subgroup G // N.Normal} → Prop :=
      fun N ↦ elementaryLayerTopAxis π hπ N = D
    let c : {N : Subgroup G // N.Normal} → ℝ :=
      elementaryLayerAxisCoefficient p π A E
    have hsplit := Fintype.sum_subtype_add_sum_subtype P c
    have hrest : 0 ≤ ∑ N : {N : {N : Subgroup G // N.Normal} // ¬ P N},
        c N.1 := Finset.sum_nonneg (fun N _ ↦
          elementaryLayerAxisCoefficient_nonneg p π A E N.1)
    have hle : (∑ N : {N : {N : Subgroup G // N.Normal} // P N}, c N.1) ≤
        ∑ N : {N : Subgroup G // N.Normal}, c N :=
      (le_add_of_nonneg_right hrest).trans hsplit.le
    simpa only [P, c] using hle

/-- Forgetting the fixed-top fibre still gives the section-capacity datum
used by the one-axis Schur estimate. -/
def sectionBound
    (H : ElementaryLayerJointCapacityBound p π hπ A E) :
    ElementaryLayerSectionCapacityBound p π A E where
  capacity := H.capacity
  capacity_nonneg := H.capacity_nonneg
  section_capacity := H.section_capacity

/-- One axis, retaining the exact top quotient indexed by its literal top
normal subgroup. -/
theorem axis_epi_le_exact_top
    (H : ElementaryLayerJointCapacityBound p π hπ A E)
    (N : {N : Subgroup G // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
      (Nat.card (GroupEpimorphism J
          (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
        (elementaryLayerAxisCoefficient p π A E N *
          (p : ℝ) ^ (H.capacity * ((b : ℝ) / p))) := by
  letI : Finite (E.sectionRepresentation π A N.1) :=
    Finite.of_surjective (E.normalSpace π A N.1).mkQ
      (E.normalSpace π A N.1).mkQ_surjective
  have hlift := fusionEpimorphism_survival_card_le_schur_of_permutation_source
    p J (OriginalKernelModuleChart.base π N.1)
      (OriginalKernelModuleChart.base_surjective π N.1)
      (E.sectionRepresentation π A N.1) (E.quotientChart π A N.1)
      (fun _ => True)
  have hcard : Nat.card {f : GroupEpimorphism J (G ⧸ N.1) // True} =
      Nat.card (GroupEpimorphism J (G ⧸ N.1)) := by simp
  rw [hcard] at hlift
  apply hlift.trans
  let K : Subgroup B := (π.ker ⊔ N.1).map π
  letI : K.Normal := Subgroup.Normal.map
    (show (π.ker ⊔ N.1).Normal from inferInstance) π hπ
  let e : (G ⧸ (π.ker ⊔ N.1)) ≃* (B ⧸ K) :=
    quotientEquivOfKernelLe π hπ (π.ker ⊔ N.1) le_sup_left
  have htop : Nat.card (GroupEpimorphism J (G ⧸ (π.ker ⊔ N.1))) =
      Nat.card (GroupEpimorphism J (B ⧸ K)) := by
    exact fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e
  rw [htop]
  apply mul_le_mul_of_nonneg_left
  · apply mul_le_mul_of_nonneg_left
    · apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (Fact.out : p.Prime).one_lt.le
      · have hb : 0 ≤ (b : ℝ) / p := by positivity
        exact mul_le_mul_of_nonneg_right (H.section_capacity N) hb
    · positivity
  · positivity

/-- **Fixed-top joint elementary envelope.**  Every top normal axis occurs
once in `completeQuotientWeight B J`; all original intersections and
extension fibres above it are paid by the uniform joint coefficient. -/
theorem completeQuotientWeight_le
    (H : ElementaryLayerJointCapacityBound p π hπ A E)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      H.coefficient * (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) *
        completeQuotientWeight (R := B) J := by
  classical
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    (∑ N : {N : Subgroup G // N.Normal},
        (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ)) ≤
      ∑ N : {N : Subgroup G // N.Normal},
        (Nat.card (GroupEpimorphism J
            (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
          (elementaryLayerAxisCoefficient p π A E N *
            (p : ℝ) ^ (H.capacity * ((b : ℝ) / p))) :=
      Finset.sum_le_sum (fun N _ => H.axis_epi_le_exact_top p π hπ A E N J)
    _ = ∑ D : {D : Subgroup B // D.Normal},
        ∑ N : {N : {N : Subgroup G // N.Normal} //
            elementaryLayerTopAxis π hπ N = D},
          (Nat.card (GroupEpimorphism J
              (B ⧸ (elementaryLayerTopAxis π hπ N.1).1)) : ℝ) *
            (elementaryLayerAxisCoefficient p π A E N.1 *
              (p : ℝ) ^ (H.capacity * ((b : ℝ) / p))) := by
      symm
      simpa only [Subtype.forall, Subtype.coe_eta] using
        (Fintype.sum_fiberwise
          (elementaryLayerTopAxis π hπ)
          (fun N : {N : Subgroup G // N.Normal} =>
            (Nat.card (GroupEpimorphism J
                (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
              (elementaryLayerAxisCoefficient p π A E N *
                (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)))))
    _ = ∑ D : {D : Subgroup B // D.Normal},
        (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
          (∑ N : {N : {N : Subgroup G // N.Normal} //
              elementaryLayerTopAxis π hπ N = D},
            elementaryLayerAxisCoefficient p π A E N.1 *
              (p : ℝ) ^ (H.capacity * ((b : ℝ) / p))) := by
      apply Finset.sum_congr rfl
      intro D _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      rw [N.2]
    _ ≤ ∑ D : {D : Subgroup B // D.Normal},
        (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
          (H.coefficient *
            (p : ℝ) ^ (H.capacity * ((b : ℝ) / p))) := by
      apply Finset.sum_le_sum
      intro D _
      apply mul_le_mul_of_nonneg_left
      · calc
          ∑ N : {N : {N : Subgroup G // N.Normal} //
              elementaryLayerTopAxis π hπ N = D},
              elementaryLayerAxisCoefficient p π A E N.1 *
                (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) =
            (∑ N : {N : {N : Subgroup G // N.Normal} //
                elementaryLayerTopAxis π hπ N = D},
                elementaryLayerAxisCoefficient p π A E N.1) *
              (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) := by
                rw [Finset.sum_mul]
          _ ≤ H.coefficient *
              (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) :=
            mul_le_mul_of_nonneg_right (H.fixed_top_fibre D) (by positivity)
      · positivity
    _ = H.coefficient *
        (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) *
          (↑(∑ D : {D : Subgroup B // D.Normal},
            Nat.card (GroupEpimorphism J (B ⧸ D.1))) : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _
      ring

end ElementaryLayerJointCapacityBound
end SymmetricSubgroupAsymptotics

end
