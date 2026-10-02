import SymmetricSubgroupAsymptotics.FixedTargetElementaryLayerEnvelope

/-!
# A generator-sensitive complete envelope for one elementary layer

`FixedTargetElementaryLayerEnvelope` bounds every descended kernel section by
the dimension of the ambient elementary kernel.  For an imprimitive affine
block kernel this loses the induced-module saving.  The theorem below keeps
the same literal normal axis and the same complete top source, but lets the
caller supply one uniform Schur-capacity bound for all descended sections.

This is the exact place where a module-generator theorem enters the counting
argument.  Normal subgroups, nonsplit extensions, restricted lifts and
cohomology fibres remain in the already proved one-layer incidence theorem;
only its exponent is sharpened.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (π : G →* B) (hπ : Function.Surjective π)
variable (A : Rep (ZMod p) B) [Finite A]
variable (E : OriginalKernelModuleChart π A)

/-- One real number bounding the Schur capacity of every literal descended
kernel section.  Keeping this as a separate structure makes clear that the
bound is required simultaneously on all original normal axes. -/
structure ElementaryLayerSectionCapacityBound where
  capacity : ℝ
  capacity_nonneg : 0 ≤ capacity
  section_capacity : ∀ N : {N : Subgroup G // N.Normal},
    representationSchurCapacity
      (E.sectionRepresentation π A N.1).ρ ≤ capacity

namespace ElementaryLayerSectionCapacityBound

include hπ

/-- One original normal axis with a supplied generator-sensitive capacity.
The target above the elementary section is still charged to the complete
quotient weight of the literal top `B`. -/
theorem axis_epi_le
    (H : ElementaryLayerSectionCapacityBound p π A E)
    (N : {N : Subgroup G // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
      completeQuotientWeight (R := B) J *
        ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
          Nat.card (groupCohomology.H1
            (E.sectionRepresentation π A N.1)) *
          (p : ℝ) ^ (H.capacity * ((b : ℝ) / p))) := by
  letI : Finite (E.sectionRepresentation π A N.1) :=
    Finite.of_surjective (E.normalSpace π A N.1).mkQ
      (E.normalSpace π A N.1).mkQ_surjective
  have h := fusionEpimorphism_survival_card_le_schur_of_permutation_source
    p J (OriginalKernelModuleChart.base π N.1)
      (OriginalKernelModuleChart.base_surjective π N.1)
      (E.sectionRepresentation π A N.1) (E.quotientChart π A N.1)
      (fun _ => True)
  have hcard : Nat.card {f : GroupEpimorphism J (G ⧸ N.1) // True} =
      Nat.card (GroupEpimorphism J (G ⧸ N.1)) := by simp
  rw [hcard] at h
  apply h.trans
  have htop := elementaryLayer_top_epi_le_completeQuotientWeight
    π hπ N J
  apply mul_le_mul htop
  · apply mul_le_mul_of_nonneg_left
    · apply Real.rpow_le_rpow_of_exponent_le
      · exact_mod_cast (Fact.out : p.Prime).one_lt.le
      · have hb : 0 ≤ (b : ℝ) / p := by positivity
        exact mul_le_mul_of_nonneg_right (H.section_capacity N) hb
    · positivity
  · positivity
  · exact completeQuotientWeight_nonneg J

/-- Complete one-layer envelope with the refined capacity.  The finite
coefficient is exactly the same sum of section and `H¹` fibres as in the
dimension bound; it is paid once before the complete top weight. -/
theorem completeQuotientWeight_le
    (H : ElementaryLayerSectionCapacityBound p π A E)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      elementaryLayerEnvelopeConstant p π A E *
        (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) *
        completeQuotientWeight (R := B) J := by
  letI : Fintype {N : Subgroup G // N.Normal} :=
    Subtype.fintype Subgroup.Normal
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    (∑ N : {N : Subgroup G // N.Normal},
        (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ)) ≤
      ∑ N : {N : Subgroup G // N.Normal},
        completeQuotientWeight (R := B) J *
          ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
            Nat.card (groupCohomology.H1
              (E.sectionRepresentation π A N.1)) *
            (p : ℝ) ^ (H.capacity * ((b : ℝ) / p))) :=
      Finset.sum_le_sum (fun N _ => H.axis_epi_le p π hπ A E N J)
    _ = elementaryLayerEnvelopeConstant p π A E *
        (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) *
        completeQuotientWeight (R := B) J := by
      unfold elementaryLayerEnvelopeConstant
      calc
        ∑ N : {N : Subgroup G // N.Normal},
            completeQuotientWeight (R := B) J *
              ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
                Nat.card (groupCohomology.H1
                  (E.sectionRepresentation π A N.1)) *
                (p : ℝ) ^ (H.capacity * ((b : ℝ) / p))) =
          ∑ N : {N : Subgroup G // N.Normal},
            ((Nat.card (E.sectionRepresentation π A N.1) : ℝ) *
              Nat.card (groupCohomology.H1
                (E.sectionRepresentation π A N.1))) *
              ((p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) *
                completeQuotientWeight (R := B) J) := by
            apply Finset.sum_congr rfl
            intro N _
            ring
        _ = _ := by
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro N _
          ring

end ElementaryLayerSectionCapacityBound

end SymmetricSubgroupAsymptotics

end
