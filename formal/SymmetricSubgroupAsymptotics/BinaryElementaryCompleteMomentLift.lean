import SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorColdCount
import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHotTail
import SymmetricSubgroupAsymptotics.BinaryKernelRankTailNumerics
import SymmetricSubgroupAsymptotics.OriginalKernelUniformDualSections
import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateTemplate

/-! A cold-rank complete-moment transfer through any ACTUAL elementary
binary kernel with its original equivariant module chart.
Every original normal denominator is retained. Cold sources keep the full
complete quotient weight of the same actual top; hot sources retain every
map and their finite-index rank tail. No classification or inner source
estimate is assumed by the transfer theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryElementaryCompleteMomentLift
open Non2UnipotentPrefixFiniteMenu OriginalKernelModuleChart

private theorem variable_cold_sum_le
    {Q T : Type} [Group Q] [Finite Q] [Group T] [Finite T]
    (m : ℕ) (hQ : Nat.card Q ≤ 2^m) (b : ℕ)
    (cold : Subgroup (Equiv.Perm (Fin b)) → ℝ) (hcold : ∀ J,0 ≤ cold J)
    (hbound : ∀ J,¬FiniteTopKernelRankHot T (51/200) J →
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤ cold J) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J Q) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 (m+Nat.card T) b + ∑ J,cold J := by
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop := FiniteTopKernelRankHot T (51/200)
  have hh := finiteTopKernelRankHot51_epi_sum_le T Q m hQ b
  have hc : (∑ J ∈ Finset.univ.filter (fun J => ¬hot J),
      (Nat.card (GroupEpimorphism J Q) : ℝ)) ≤ ∑ J,cold J := by
    calc
      _ ≤ ∑ J ∈ Finset.univ.filter (fun J => ¬hot J),cold J :=
        Finset.sum_le_sum (fun J hJ => hbound J (Finset.mem_filter.mp hJ).2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun J _ _ => hcold J)
  rw [←Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  exact add_le_add (by simpa only [BinaryKernelRankTailNumerics.raw,one_mul] using hh) hc

private theorem coefficient_le {Q R : Type} [Group Q] [Finite Q] [Group R] [Finite R]
    (m t : ℕ) (hQ : Nat.card Q ≤ 2^m) (hR : Nat.card R ≤ 2^t) :
    ((Nat.card Q^Nat.log 2 (Nat.card R) : ℕ) : ℝ) ≤ (2 : ℝ)^(m*t) := by
  have ht : Nat.log 2 (Nat.card R) ≤ t := by
    have hh : Nat.card R < 2^(t+1) := hR.trans_lt
      (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))
    have hl := Nat.log_lt_of_lt_pow (Nat.card_pos (α := R)).ne' hh
    omega
  have hp : Nat.card Q^Nat.log 2 (Nat.card R) ≤ 2^(m*t) := calc
    _ ≤ (2^m)^Nat.log 2 (Nat.card R) := Nat.pow_le_pow_left hQ _
    _ ≤ (2^m)^t := Nat.pow_le_pow_right (by positivity) ht
    _ = _ := by rw [←pow_mul]
  exact_mod_cast hp

variable {U B : Type} [Group U] [Finite U] [Group B] [Finite B]
    (pi : U →* B) (hpi : Function.Surjective pi)
    (A : Rep.{0} (ZMod 2) B)
    (E : OriginalKernelModuleChart pi A)

include pi hpi E in
/-- One actual normal quotient retains the COMPLETE original top moment,
with no choice of an optimized top quotient depending on its source. -/
theorem axis_sum_le {c : ℕ}
    (hu : UniformSubrepresentationGeneratorBound A.ρ.dual c)
    (m t : ℕ) (hU : Nat.card U ≤ 2^m) (hT : Nat.card B ≤ 2^t)
    (N : Subgroup U) [N.Normal] (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),(Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ)) ≤
      BinaryKernelRankTailNumerics.raw 1 (m+2^t) b +
        ((2 : ℝ)^(m*t)*(2 : ℝ)^(((51/200 : ℝ)*c)*b))*
          ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := B) J := by
  let f := sectionTop pi N hpi
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) q
    exact ⟨pi g,sectionTop_apply pi N hpi g⟩
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hq : Nat.card (U ⧸ N) ≤ 2^m :=
    (Nat.card_le_card_of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)).trans hU
  have hr : Nat.card (U ⧸ (pi.ker ⊔ N)) ≤ 2^t :=
    (Nat.card_le_card_of_surjective f hf).trans hT
  let K : ℝ := (2 : ℝ)^(m*t)*(2 : ℝ)^(((51/200 : ℝ)*c)*b)
  have hc (J : Subgroup (Equiv.Perm (Fin b)))
      (hJ : ¬FiniteTopKernelRankHot (U ⧸ (pi.ker ⊔ N)) (51/200) J) :
      (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) ≤
        K*completeQuotientWeight (R := B) J := by
    have hh := FiniteTopBinaryDualKernelGeneratorColdCount.cold_card_le
      (base pi N) (base_surjective pi N) (E.sectionRepresentation pi A N)
      (E.quotientChart pi A N)
      (E.sectionDualGeneratedBy_of_uniform pi A hpi hu N) b J hJ
    have hepi : (Nat.card (GroupEpimorphism J (U ⧸ (pi.ker ⊔ N))) : ℝ) ≤
        completeQuotientWeight (R := B) J :=
      card_groupEpimorphism_le_completeQuotientWeight J ⟨f.ker,inferInstance⟩ e.symm
    have hcoeff := coefficient_le m t hq hr
    exact hh.trans (by
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul hepi hcoeff (by positivity) (completeQuotientWeight_nonneg J))
        (show 0 ≤ (2 : ℝ)^(((51/200 : ℝ)*c)*b) by positivity)
      apply hmul.trans_eq
      dsimp [K]
      ring)
  have hh := variable_cold_sum_le (T := U ⧸ (pi.ker ⊔ N)) m hq b
    (fun J => K*completeQuotientWeight (R := B) J)
    (fun J => mul_nonneg (by dsimp [K]; positivity) (completeQuotientWeight_nonneg J)) hc
  rw [←Finset.mul_sum] at hh
  apply hh.trans
  apply add_le_add _ le_rfl
  unfold BinaryKernelRankTailNumerics.raw
  simp only [one_mul]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact pow_le_pow_right₀
    (by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos b)) (Nat.add_le_add_left hr m)

include pi hpi E in
/-- All literal normal axes are summed BEFORE applying any bound on the
inner complete moment. Repeated residual top axes are charged in a fixed
target coefficient; they are never silently identified or discarded. -/
theorem complete_moment_le {c : ℕ}
    (hu : UniformSubrepresentationGeneratorBound A.ρ.dual c)
    (m t : ℕ) (hU : Nat.card U ≤ 2^m) (hT : Nat.card B ≤ 2^t) (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := U) J) ≤
      (Nat.card {N : Subgroup U // N.Normal} : ℝ)*
        (BinaryKernelRankTailNumerics.raw 1 (m+2^t) b +
          ((2 : ℝ)^(m*t)*(2 : ℝ)^(((51/200 : ℝ)*c)*b))*
            ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := B) J) := by
  have hswap :
      (∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := U) J)=
      ∑ N : {N : Subgroup U // N.Normal},
        ∑ J : Subgroup (Equiv.Perm (Fin b)),
          (Nat.card (GroupEpimorphism J (U ⧸ N.val)) : ℝ) := by
    unfold completeQuotientWeight completeQuotientCount
    simp only [Nat.cast_sum]
    rw [Finset.sum_comm]
  rw [hswap]
  calc
    _ ≤ ∑ N : {N : Subgroup U // N.Normal},
        (BinaryKernelRankTailNumerics.raw 1 (m+2^t) b +
          ((2 : ℝ)^(m*t)*(2 : ℝ)^(((51/200 : ℝ)*c)*b))*
            ∑ J : Subgroup (Equiv.Perm (Fin b)),completeQuotientWeight (R := B) J) := by
      apply Finset.sum_le_sum
      intro N _
      letI : N.val.Normal := N.property
      exact axis_sum_le pi hpi A E hu m t hU hT N.val b
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]

end SymmetricSubgroupAsymptotics.BinaryElementaryCompleteMomentLift
