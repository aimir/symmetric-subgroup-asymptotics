import SymmetricSubgroupAsymptotics.OriginalPrimeCentralCutFusion
import SymmetricSubgroupAsymptotics.JointElementaryLayerEnvelope

/-!
# Joint elementary envelopes after the invariant prime cut

For every literal normal axis, cut the full invariant subspace from the
actual elementary section.  The cut is central in the original extension.
Its dimension is retained as a same-source prime-character marker, while the
ordinary Schur exponent is charged only to the quotient representation.
Normal axes are still regrouped by their exact top axis before the finite
coefficient is extracted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

attribute [-instance] originalNormalFintype

private def quotientEquivOfKernelLePrimeCut {U R : Type*} [Group U] [Group R]
    (f : U →* R) (hf : Function.Surjective f)
    (N : Subgroup U) [N.Normal] (hker : f.ker ≤ N) :
    letI : (N.map f).Normal := Subgroup.Normal.map
      (show N.Normal from inferInstance) f hf
    U ⧸ N ≃* R ⧸ N.map f := by
  letI : (N.map f).Normal := Subgroup.Normal.map
    (show N.Normal from inferInstance) f hf
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

/-- The full literal invariant subspace in one descended normal section. -/
def elementaryLayerInvariantCut
    (N : {N : Subgroup G // N.Normal}) :
    {C : Submodule (ZMod p) (E.sectionRepresentation π A N.1) //
      C ≤ (E.sectionRepresentation π A N.1).ρ.invariants} :=
  ⟨(E.sectionRepresentation π A N.1).ρ.invariants, le_rfl⟩

/-- Finite coefficient remaining below the literal invariant cut. -/
def elementaryLayerPrimeCutCoefficient
    (N : {N : Subgroup G // N.Normal}) : ℝ :=
  OriginalPrimeCentralCutFusion.liftConstant p
    (E.sectionRepresentation π A N.1)
    (elementaryLayerInvariantCut p π A E N)

/-- The quotient Schur capacity after removing the literal invariant cut. -/
def elementaryLayerPrimeCutCapacity
    (N : {N : Subgroup G // N.Normal}) : ℝ :=
  OriginalPrimeCentralCutFusion.capacity p
    (E.sectionRepresentation π A N.1)
    (elementaryLayerInvariantCut p π A E N)

/-- A simultaneous central-cut capacity over every literal normal axis.
`fixedCapacity` is the number of same-source prime-character columns;
`quotientCapacity` is the remaining Schur exponent. -/
structure PrimeCentralLayerJointCapacityBound where
  fixedCapacity : ℕ
  quotientCapacity : ℝ
  quotientCapacity_nonneg : 0 ≤ quotientCapacity
  fixed_le : ∀ N : {N : Subgroup G // N.Normal},
    Module.finrank (ZMod p)
      (E.sectionRepresentation π A N.1).ρ.invariants ≤ fixedCapacity
  quotient_capacity_le : ∀ N : {N : Subgroup G // N.Normal},
    elementaryLayerPrimeCutCapacity p π A E N ≤ quotientCapacity
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  fixed_top_fibre : ∀ D : {D : Subgroup B // D.Normal},
    (∑ N : {N : {N : Subgroup G // N.Normal} //
        elementaryLayerTopAxis π hπ N = D},
      elementaryLayerPrimeCutCoefficient p π A E N.1) ≤ coefficient

namespace PrimeCentralLayerJointCapacityBound

variable (H : PrimeCentralLayerJointCapacityBound p π hπ A E)

include hπ

/-- One literal normal axis, with the invariant prime row kept on the same
source and the exact top quotient unchanged. -/
theorem axis_epi_le_exact_top_primeCut
    (N : {N : Subgroup G // N.Normal})
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ) ≤
      (Nat.card (GroupEpimorphism J
          (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
        (p : ℝ) ^ (H.fixedCapacity *
          Module.finrank (ZMod p) (PrimeCharacters p J)) *
        (elementaryLayerPrimeCutCoefficient p π A E N *
          (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ))) := by
  let M := E.sectionRepresentation π A N.1
  let C := elementaryLayerInvariantCut p π A E N
  let α := OriginalKernelModuleChart.base π N.1
  let Eₙ := E.quotientChart π A N.1
  letI : Finite M := Finite.of_surjective
    (E.normalSpace π A N.1).mkQ
      (E.normalSpace π A N.1).mkQ_surjective
  have hraw := OriginalPrimeCentralCutFusion.original_survival_card_le
    p M C α (OriginalKernelModuleChart.base_surjective π N.1) Eₙ J
      (fun _ => True)
  rw [Nat.card_subtype_true] at hraw
  have hfixed : (p : ℝ) ^
      (Module.finrank (ZMod p) C.1 *
        Module.finrank (ZMod p) (PrimeCharacters p J)) ≤
      (p : ℝ) ^
        (H.fixedCapacity *
          Module.finrank (ZMod p) (PrimeCharacters p J)) := by
    apply pow_le_pow_right₀
    · exact_mod_cast (Fact.out : p.Prime).one_lt.le
    · exact Nat.mul_le_mul_right
        (Module.finrank (ZMod p) (PrimeCharacters p J)) (H.fixed_le N)
  have hquot : (p : ℝ) ^
      ((elementaryLayerPrimeCutCapacity p π A E N / p) * (b : ℝ)) ≤
      (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
    have hb : 0 ≤ (b : ℝ) := by positivity
    have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (H.quotient_capacity_le N) hp.le) hb
  let K : Subgroup B := (π.ker ⊔ N.1).map π
  letI : K.Normal := Subgroup.Normal.map
    (show (π.ker ⊔ N.1).Normal from inferInstance) π hπ
  let e : (G ⧸ (π.ker ⊔ N.1)) ≃* (B ⧸ K) :=
    quotientEquivOfKernelLePrimeCut π hπ (π.ker ⊔ N.1) le_sup_left
  have htop : Nat.card (GroupEpimorphism J (G ⧸ (π.ker ⊔ N.1))) =
      Nat.card (GroupEpimorphism J
        (B ⧸ (elementaryLayerTopAxis π hπ N).1)) := by
    change _ = Nat.card (GroupEpimorphism J (B ⧸ K))
    exact fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e
  rw [← htop]
  unfold OriginalPrimeCentralCutFusion.momentWeight at hraw
  unfold fusionPrimeCentralPrefixWeight at hraw
  apply hraw.trans
  have hL : 0 ≤ elementaryLayerPrimeCutCoefficient p π A E N :=
    OriginalPrimeCentralCutFusion.liftConstant_nonneg p M C
  have htop0 : 0 ≤ (Nat.card (GroupEpimorphism J
      (G ⧸ (π.ker ⊔ N.1))) : ℝ) := by positivity
  have hmark0 : 0 ≤ (p : ℝ) ^
      (Module.finrank (ZMod p) C.1 *
        Module.finrank (ZMod p) (PrimeCharacters p J)) := by positivity
  have houter0 : 0 ≤ elementaryLayerPrimeCutCoefficient p π A E N *
      (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) :=
    mul_nonneg hL (by positivity)
  calc
    _ ≤ elementaryLayerPrimeCutCoefficient p π A E N *
        (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) *
          ((Nat.card (GroupEpimorphism J
              (G ⧸ (π.ker ⊔ N.1))) : ℝ) *
            (p : ℝ) ^
              (Module.finrank (ZMod p) C.1 *
                Module.finrank (ZMod p) (PrimeCharacters p J))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hquot hL)
        (mul_nonneg htop0 hmark0)
    _ ≤ elementaryLayerPrimeCutCoefficient p π A E N *
        (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) *
          ((Nat.card (GroupEpimorphism J
              (G ⧸ (π.ker ⊔ N.1))) : ℝ) *
            (p : ℝ) ^
              (H.fixedCapacity *
                Module.finrank (ZMod p) (PrimeCharacters p J))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hfixed htop0) houter0
    _ = _ := by ring

/-- Fixed-top sum after the invariant cut.  The prime-character weight is
extracted only after all original normal axes above that top are joined. -/
theorem completeQuotientWeight_le_primeCut
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      H.coefficient *
        (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) *
        ((p : ℝ) ^ (H.fixedCapacity *
          Module.finrank (ZMod p) (PrimeCharacters p J)) *
          completeQuotientWeight (R := B) J) := by
  classical
  unfold completeQuotientWeight completeQuotientCount
  rw [Nat.cast_sum]
  calc
    (∑ N : {N : Subgroup G // N.Normal},
        (Nat.card (GroupEpimorphism J (G ⧸ N.1)) : ℝ)) ≤
      ∑ N : {N : Subgroup G // N.Normal},
        (Nat.card (GroupEpimorphism J
            (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
          (p : ℝ) ^ (H.fixedCapacity *
            Module.finrank (ZMod p) (PrimeCharacters p J)) *
          (elementaryLayerPrimeCutCoefficient p π A E N *
            (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ))) :=
      Finset.sum_le_sum (fun N _ =>
        H.axis_epi_le_exact_top_primeCut p π hπ A E N J)
    _ = ∑ D : {D : Subgroup B // D.Normal},
        ∑ N : {N : {N : Subgroup G // N.Normal} //
            elementaryLayerTopAxis π hπ N = D},
          (Nat.card (GroupEpimorphism J
              (B ⧸ (elementaryLayerTopAxis π hπ N.1).1)) : ℝ) *
            (p : ℝ) ^ (H.fixedCapacity *
              Module.finrank (ZMod p) (PrimeCharacters p J)) *
            (elementaryLayerPrimeCutCoefficient p π A E N.1 *
              (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ))) := by
      symm
      simpa only [Subtype.forall, Subtype.coe_eta] using
        (Fintype.sum_fiberwise
          (elementaryLayerTopAxis π hπ)
          (fun N : {N : Subgroup G // N.Normal} =>
            (Nat.card (GroupEpimorphism J
                (B ⧸ (elementaryLayerTopAxis π hπ N).1)) : ℝ) *
              (p : ℝ) ^ (H.fixedCapacity *
                Module.finrank (ZMod p) (PrimeCharacters p J)) *
              (elementaryLayerPrimeCutCoefficient p π A E N *
                (p : ℝ) ^
                  ((H.quotientCapacity / p) * (b : ℝ)))))
    _ = ∑ D : {D : Subgroup B // D.Normal},
        ∑ N : {N : {N : Subgroup G // N.Normal} //
            elementaryLayerTopAxis π hπ N = D},
          (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
            (p : ℝ) ^ (H.fixedCapacity *
              Module.finrank (ZMod p) (PrimeCharacters p J)) *
            (elementaryLayerPrimeCutCoefficient p π A E N.1 *
              (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ))) := by
      apply Finset.sum_congr rfl
      intro D _
      apply Finset.sum_congr rfl
      intro N _
      rw [N.2]
    _ ≤ ∑ D : {D : Subgroup B // D.Normal},
        (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
          (p : ℝ) ^ (H.fixedCapacity *
            Module.finrank (ZMod p) (PrimeCharacters p J)) *
          (H.coefficient *
            (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ))) := by
      apply Finset.sum_le_sum
      intro D _
      calc
        (∑ N : {N : {N : Subgroup G // N.Normal} //
            elementaryLayerTopAxis π hπ N = D},
            (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
              (p : ℝ) ^ (H.fixedCapacity *
                Module.finrank (ZMod p) (PrimeCharacters p J)) *
              (elementaryLayerPrimeCutCoefficient p π A E N.1 *
                (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)))) =
          (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
            (p : ℝ) ^ (H.fixedCapacity *
              Module.finrank (ZMod p) (PrimeCharacters p J)) *
            (∑ N : {N : {N : Subgroup G // N.Normal} //
                elementaryLayerTopAxis π hπ N = D},
                elementaryLayerPrimeCutCoefficient p π A E N.1 *
                  (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ (Nat.card (GroupEpimorphism J (B ⧸ D.1)) : ℝ) *
            (p : ℝ) ^ (H.fixedCapacity *
              Module.finrank (ZMod p) (PrimeCharacters p J)) *
            (H.coefficient *
              (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ))) := by
          apply mul_le_mul_of_nonneg_left
          · calc
            (∑ N : {N : {N : Subgroup G // N.Normal} //
                elementaryLayerTopAxis π hπ N = D},
                elementaryLayerPrimeCutCoefficient p π A E N.1 *
                  (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ))) =
              (∑ N : {N : {N : Subgroup G // N.Normal} //
                  elementaryLayerTopAxis π hπ N = D},
                  elementaryLayerPrimeCutCoefficient p π A E N.1) *
                (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) := by
                  rw [Finset.sum_mul]
            _ ≤ H.coefficient *
                (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) :=
              mul_le_mul_of_nonneg_right (H.fixed_top_fibre D) (by positivity)
          · positivity
    _ = H.coefficient *
        (p : ℝ) ^ ((H.quotientCapacity / p) * (b : ℝ)) *
        ((p : ℝ) ^ (H.fixedCapacity *
          Module.finrank (ZMod p) (PrimeCharacters p J)) *
          (↑(∑ D : {D : Subgroup B // D.Normal},
            Nat.card (GroupEpimorphism J (B ⧸ D.1))) : ℝ)) := by
      rw [Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro D _
      ring

end PrimeCentralLayerJointCapacityBound
end SymmetricSubgroupAsymptotics

end
