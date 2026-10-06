import SymmetricSubgroupAsymptotics.JointElementaryLayerEnvelope

/-!
# Exact fixed-top elementary-layer regrouping

`ElementaryLayerJointCapacityBound.completeQuotientWeight_le` is the right
endpoint once every top axis is charged by one uniform capacity.  The
degree-three four-block binary cell needs one earlier stopping point: its
binary direct/carrier decision is made on the literal top normal, so the
annihilator-sensitive elementary factor must still be visible there.

This file exposes that stopping point.  The exponent on an original normal
axis is its actual descended `representationSchurCapacity`; neither the
uniform capacity nor the fixed-top coefficient has yet been applied.  The
only regrouping is the exact finite fibre of `elementaryLayerTopAxis`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/- Keep the same canonical normal-axis enumeration as
`JointElementaryLayerEnvelope`. -/
attribute [-instance] originalNormalFintype

variable (p : ℕ) [Fact p.Prime]
variable {G B : Type} [Group G] [Finite G] [Group B] [Finite B]
variable (π : G →* B) (hπ : Function.Surjective π)
variable (A : Rep (ZMod p) B) [Finite A]
variable (E : OriginalKernelModuleChart π A)

private def exactTopQuotientEquivOfKernelLe {U R : Type*}
    [Group U] [Group R]
    (f : U →* R) (hf : Function.Surjective f)
    (N : Subgroup U) [N.Normal] (hker : f.ker ≤ N) :
    letI : (N.map f).Normal :=
      Subgroup.Normal.map (show N.Normal from inferInstance) f hf
    U ⧸ N ≃* R ⧸ N.map f := by
  letI : (N.map f).Normal :=
    Subgroup.Normal.map (show N.Normal from inferInstance) f hf
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

/-- The exact elementary incidence factor on one original normal axis.
It retains the actual quotient section, its `H¹`, and its actual Schur
capacity. -/
def elementaryLayerExactAxisFactor
    (N : {N : Subgroup G // N.Normal}) (b : ℕ) : ℝ :=
  elementaryLayerAxisCoefficient p π A E N *
    (p : ℝ) ^
      (representationSchurCapacity
          (E.sectionRepresentation π A N.1).ρ * ((b : ℝ) / p))

theorem elementaryLayerExactAxisFactor_nonneg
    (N : {N : Subgroup G // N.Normal}) (b : ℕ) :
    0 ≤ elementaryLayerExactAxisFactor p π A E N b := by
  unfold elementaryLayerExactAxisFactor
  exact mul_nonneg (elementaryLayerAxisCoefficient_nonneg p π A E N)
    (Real.rpow_nonneg (Nat.cast_nonneg p) _)

omit [Finite B] in
/-- One literal original axis, with the exact descended capacity and the
exact top normal still visible. -/
theorem elementaryLayer_axis_epi_le_exact_top_exactCapacity
    (N : {N : Subgroup G // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
      (Nat.card (GroupEpimorphism J
          (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
        elementaryLayerExactAxisFactor p π A E N b := by
  letI : Finite (E.sectionRepresentation π A N.1) :=
    Finite.of_surjective (E.normalSpace π A N.1).mkQ
      (E.normalSpace π A N.1).mkQ_surjective
  have hlift := fusionEpimorphism_survival_card_le_schur_of_permutation_source
    p J (OriginalKernelModuleChart.base π N.1)
      (OriginalKernelModuleChart.base_surjective π N.1)
      (E.sectionRepresentation π A N.1) (E.quotientChart π A N.1)
      (fun _ ↦ True)
  have hcard : Nat.card {f : GroupEpimorphism J (G ⧸ N.1) // True} =
      Nat.card (GroupEpimorphism J (G ⧸ N.1)) := by simp
  rw [hcard] at hlift
  let K : Subgroup B := (π.ker ⊔ N.1).map π
  letI : K.Normal := Subgroup.Normal.map
    (show (π.ker ⊔ N.1).Normal from inferInstance) π hπ
  let e : (G ⧸ (π.ker ⊔ N.1)) ≃* (B ⧸ K) :=
    exactTopQuotientEquivOfKernelLe π hπ (π.ker ⊔ N.1) le_sup_left
  have htop : Nat.card (GroupEpimorphism J (G ⧸ (π.ker ⊔ N.1))) =
      Nat.card (GroupEpimorphism J (B ⧸ K)) :=
    fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e
  rw [htop] at hlift
  simpa only [elementaryLayerExactAxisFactor,
    elementaryLayerAxisCoefficient, mul_assoc] using hlift

/-- The exact annihilator-aware contribution over one literal top normal.
This is the quantity which has to be paired with the direct entry or carrier
slot selected on that same top axis. -/
def elementaryLayerExactTopContribution
    (D : {D : Subgroup B // D.Normal}) (b : ℕ) : ℝ :=
  ∑ N : {N : {N : Subgroup G // N.Normal} //
      elementaryLayerTopAxis π hπ N = D},
    elementaryLayerExactAxisFactor p π A E N.1 b

theorem elementaryLayerExactTopContribution_nonneg
    (D : {D : Subgroup B // D.Normal}) (b : ℕ) :
    0 ≤ elementaryLayerExactTopContribution p π hπ A E D b := by
  unfold elementaryLayerExactTopContribution
  exact Finset.sum_nonneg (fun N _ ↦
    elementaryLayerExactAxisFactor_nonneg p π A E N.1 b)

/-- On a top axis sent to a direct owner one may still apply the old uniform
capacity, but only after that axis has been selected.  Carrier axes should
keep `elementaryLayerExactTopContribution` and use their retained
annihilator instead. -/
theorem elementaryLayerExactTopContribution_le_uniform
    (H : ElementaryLayerJointCapacityBound p π hπ A E)
    (D : {D : Subgroup B // D.Normal}) (b : ℕ) :
    elementaryLayerExactTopContribution p π hπ A E D b ≤
      H.coefficient *
        (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) := by
  unfold elementaryLayerExactTopContribution
  calc
    (∑ N : {N : {N : Subgroup G // N.Normal} //
        elementaryLayerTopAxis π hπ N = D},
      elementaryLayerExactAxisFactor p π A E N.1 b) ≤
      ∑ N : {N : {N : Subgroup G // N.Normal} //
          elementaryLayerTopAxis π hπ N = D},
        elementaryLayerAxisCoefficient p π A E N.1 *
          (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) := by
      apply Finset.sum_le_sum
      intro N _
      unfold elementaryLayerExactAxisFactor
      apply mul_le_mul_of_nonneg_left
      · apply Real.rpow_le_rpow_of_exponent_le
        · exact_mod_cast (Fact.out : p.Prime).one_lt.le
        · exact mul_le_mul_of_nonneg_right (H.section_capacity N.1)
            (by positivity)
      · exact elementaryLayerAxisCoefficient_nonneg p π A E N.1
    _ = (∑ N : {N : {N : Subgroup G // N.Normal} //
          elementaryLayerTopAxis π hπ N = D},
        elementaryLayerAxisCoefficient p π A E N.1) *
          (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) := by
      rw [Finset.sum_mul]
    _ ≤ H.coefficient *
        (p : ℝ) ^ (H.capacity * ((b : ℝ) / p)) :=
      mul_le_mul_of_nonneg_right (H.fixed_top_fibre D) (by positivity)

/-- Exact fixed-top regrouping before any uniform capacity relaxation.
Every original normal occurs once, and the top quotient-map count is
multiplied by the sum of its actual elementary incidence factors. -/
theorem completeQuotientWeight_le_exactTopContributions
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      ∑ D : {D : Subgroup B // D.Normal},
        (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
          elementaryLayerExactTopContribution p π hπ A E D b := by
  classical
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    (∑ N : {N : Subgroup G // N.Normal},
        (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ)) ≤
      ∑ N : {N : Subgroup G // N.Normal},
        (Nat.card (GroupEpimorphism J
            (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
          elementaryLayerExactAxisFactor p π A E N b :=
      Finset.sum_le_sum (fun N _ ↦
        elementaryLayer_axis_epi_le_exact_top_exactCapacity
          p π hπ A E N J)
    _ = ∑ D : {D : Subgroup B // D.Normal},
        ∑ N : {N : {N : Subgroup G // N.Normal} //
            elementaryLayerTopAxis π hπ N = D},
          (Nat.card (GroupEpimorphism J
              (B ⧸ (elementaryLayerTopAxis π hπ N.1).1)) : ℝ) *
            elementaryLayerExactAxisFactor p π A E N.1 b := by
      symm
      simpa only [Subtype.forall, Subtype.coe_eta] using
        (Fintype.sum_fiberwise
          (elementaryLayerTopAxis π hπ)
          (fun N : {N : Subgroup G // N.Normal} ↦
            (Nat.card (GroupEpimorphism J
                (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
              elementaryLayerExactAxisFactor p π A E N b))
    _ = ∑ D : {D : Subgroup B // D.Normal},
        (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
          elementaryLayerExactTopContribution p π hπ A E D b := by
      apply Finset.sum_congr rfl
      intro D _
      rw [elementaryLayerExactTopContribution, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N _
      rw [N.2]

end SymmetricSubgroupAsymptotics

end
