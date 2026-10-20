import SymmetricSubgroupAsymptotics.MarkedC4ActualGlobalMarkGeneratorRank
import SymmetricSubgroupAsymptotics.MarkedC4ActualHallColumnCompression

/-! Abelian physical quotient factors are removed BEFORE applying the
improved original-factor RDT5.5 coefficients. Their entire kernel cost is
a/2, plus r for the single global marker; derived-normal cost is unchanged. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualAbelianPhysicalBlockRank
open ActualMarkZeroNormalRank ActualGlobalMarkGeneratorRank

variable {B M : Type} [Group B] [Finite B] [CommGroup M] [Finite M]
  (A : Subgroup (B × M))

def kernelMarker : (physical A).ker →* M := (mark A).comp (physical A).ker.subtype
theorem kernelMarker_injective : Function.Injective (kernelMarker A) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact (show x.val.val.1=1 from x.property).trans
      (show y.val.val.1=1 from y.property).symm
  · exact he

theorem rank_le_physical_add_column (hM : IsPGroup 2 M) :
    genRank A≤genRank (PhysicalImage A)+col M 0 := by
  let e : (physical A).ker ≃* (kernelMarker A).range :=
    MonoidHom.ofInjective (kernelMarker_injective A)
  have hk : genRank (physical A).ker≤col M 0 :=
    (genRank_le_of_surjective e.symm.toMonoidHom e.symm.surjective).trans
      ((genRank_le_col_zero (hM.to_subgroup (kernelMarker A).range)).trans
        (col_zero_subgroup_le (kernelMarker A).range))
  let eQ := QuotientGroup.quotientKerEquivRange (physical A)
  have hq : genRank (A ⧸ (physical A).ker)≤genRank (PhysicalImage A) :=
    genRank_le_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective
  have h := genRank_le_of_normal (physical A).ker
  omega

theorem abelian_marks_binary (C : Type) [CommGroup C] [Finite C]
    (hC : IsPGroup 2 C) (r : ℕ) : IsPGroup 2 (C × Marks r) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a,ha⟩ := hC.exists_card_eq
  obtain ⟨b,hb⟩ := (marks_binary r).exists_card_eq
  apply IsPGroup.of_card (n := a+b)
  rw [Nat.card_prod,ha,hb,pow_add]

/-- Actual abelian physical block and global-marker kernel rank. The
physical block's order cap, rather than a rank capacity, supplies a/2. -/
theorem rank_le_physical_add_abelian_marks
    (C : Type) [CommGroup C] [Finite C] (hC : IsPGroup 2 C) (m r : ℕ)
    (hExp : HasExp2 C (2+m)) {a : ℝ}
    (hcard : (Nat.card C : ℝ)≤(2 : ℝ)^(a/2))
    (J : Subgroup (B × (C × Marks r))) :
    (genRank J : ℝ)≤genRank (PhysicalImage J)+a/2+r := by
  have hc : (col C 0 : ℝ)≤a/2 := by
    have hmass := ActualHallColumnCompression.column_mass_le (2+m) C hExp hcard
    have hzero : (col C 0 : ℝ)≤∑ k ∈ Finset.range (2+m),(col C k : ℝ) :=
      Finset.single_le_sum (fun k hk => Nat.cast_nonneg _) (Finset.mem_range.mpr (by omega))
    exact hzero.trans hmass
  have h := rank_le_physical_add_column J (abelian_marks_binary C hC r)
  have hr : (genRank J : ℝ)≤genRank (PhysicalImage J)+(col (C × Marks r) 0 : ℝ) := by
    exact_mod_cast h
  rw [col_prod,col_cyclicFourCoordinates] at hr
  norm_num only [Nat.reduceLT,if_true,Nat.cast_add] at hr
  linarith

end SymmetricSubgroupAsymptotics.MarkedC4.ActualAbelianPhysicalBlockRank
