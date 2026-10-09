import SymmetricSubgroupAsymptotics.CentralBinaryRecursiveCompleteQuotientComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSource

/-!
# QStar comparison for a two-sign ternary section

The geometric two-sign argument produces a ternary section which maps onto
the literal `S₃ ≀ C₂` comparator.  Its action kernel has order at most four
and admits two central binary factors.  This file packages the purely
group-theoretic conclusion: every such section, including all of its normal
quotients, is controlled by the single literal `QStar` comparator.

The construction uses the three displayed quotient maps of `QStar` onto
`S₃ ≀ C₂`, `(S₃ ≀ C₂) × C₂`, and the whole abstract `QStar` product.  Thus
no catalogue of normal subgroups of the ternary section is required.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeThreeFourBlockTwoSignComparator

private abbrev C2 := Multiplicative (ZMod 2)

/-- A central binary extension of the literal ternary wreath comparator is
controlled by the first two quotient maps of `QStar`. -/
noncomputable def centralWreathGlobalComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (hcentral : ∀ z ∈ pi.ker, ∀ x : R, z * x = x * z)
    (hkernel : Nat.card pi.ker ≤ 2) :
    CentralBinaryGlobalComparison QStarGroup R DegreeSixS3Wreath.G where
  projection := pi
  projection_surjective := hpi
  central_kernel := hcentral
  kernel_card_le_two := hkernel
  baseQuotient := qStarToWreath
  baseQuotient_surjective := qStarToWreath_surjective
  productQuotient := qStarToWreathC2
  productQuotient_surjective := qStarToWreathC2_surjective

/-- Recursive comparison for one central binary extension of the literal
ternary wreath comparator. -/
noncomputable def centralWreathComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (hcentral : ∀ z ∈ pi.ker, ∀ x : R, z * x = x * z)
    (hkernel : Nat.card pi.ker ≤ 2) :
    CentralBinaryRecursiveComparison QStarGroup R DegreeSixS3Wreath.G :=
  CentralBinaryRecursiveComparison.ofGlobal
    (centralWreathGlobalComparison pi hpi hcentral hkernel)

/-- The same extension after adjoining one binary factor.  The final
required target is definitionally the whole abstract `QStar` product. -/
noncomputable def centralWreathProductComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (hcentral : ∀ z ∈ pi.ker, ∀ x : R, z * x = x * z)
    (hkernel : Nat.card pi.ker ≤ 2) :
    CentralBinaryRecursiveComparison QStarGroup (R × C2)
      (DegreeSixS3Wreath.G × C2) := by
  let D := centralWreathComparison pi hpi hcentral hkernel
  apply D.prodC2 1
  intro b J
  simpa only [Nat.cast_one, one_mul] using
    completeQuotientWeight_le_of_surjective
      (MonoidHom.id QStarGroup) Function.surjective_id J

/-- Descend the ternary action map through the first central factor of its
kernel. -/
def wreathMapAfterCentralAxis
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (S : BinaryNormalKernelCentralSeries R pi.ker) :
    R ⧸ S.C →* DegreeSixS3Wreath.G :=
  QuotientGroup.lift S.C pi S.C_le_K

theorem wreathMapAfterCentralAxis_surjective
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker) :
    Function.Surjective (wreathMapAfterCentralAxis pi S) := by
  intro t
  obtain ⟨r, rfl⟩ := hpi t
  exact ⟨QuotientGroup.mk' S.C r, rfl⟩

theorem wreathMapAfterCentralAxis_central_kernel
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (S : BinaryNormalKernelCentralSeries R pi.ker) :
    ∀ z ∈ (wreathMapAfterCentralAxis pi S).ker,
      ∀ x, z * x = x * z := by
  intro z hz x
  have hz' : z ∈ pi.ker.map (QuotientGroup.mk' S.C) := by
    simpa only [wreathMapAfterCentralAxis, QuotientGroup.ker_lift] using hz
  exact Subgroup.mem_center_iff.mp (S.quotientKernel_le_center hz') x

theorem wreathMapAfterCentralAxis_kernel_card_le
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4) :
    Nat.card (wreathMapAfterCentralAxis pi S).ker ≤ 2 := by
  let K := pi.ker
  let q : R →* R ⧸ S.C := QuotientGroup.mk' S.C
  let L : Subgroup (R ⧸ S.C) := K.map q
  let f : K →* L := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  have hker : f.ker = S.C.subgroupOf K := by
    rw [MonoidHom.ker_subgroupMap, QuotientGroup.ker_mk']
  have hkerCard : Nat.card f.ker = 2 := by
    rw [hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe S.C_le_K).toEquiv,
      S.C_card]
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hkerCard] at hcard
  have hKcard : Nat.card K ≤ 4 := hkernel
  have hLcard : Nat.card L ≤ 2 := by omega
  have hkerLift : (wreathMapAfterCentralAxis pi S).ker = L := by
    simpa only [wreathMapAfterCentralAxis, K, q, L,
      QuotientGroup.ker_lift]
  rw [hkerLift]
  exact hLcard

/-- Comparison of the first central quotient with `QStar`. -/
noncomputable def firstCentralWreathComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4) :
    CentralBinaryRecursiveComparison QStarGroup (R ⧸ S.C)
      DegreeSixS3Wreath.G :=
  centralWreathComparison
    (wreathMapAfterCentralAxis pi S)
    (wreathMapAfterCentralAxis_surjective pi hpi S)
    (wreathMapAfterCentralAxis_central_kernel pi S)
    (wreathMapAfterCentralAxis_kernel_card_le pi S hkernel)

/-- Comparison of the first central quotient times `C₂` with `QStar`. -/
noncomputable def firstCentralWreathProductComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4) :
    CentralBinaryRecursiveComparison QStarGroup ((R ⧸ S.C) × C2)
      (DegreeSixS3Wreath.G × C2) :=
  centralWreathProductComparison
    (wreathMapAfterCentralAxis pi S)
    (wreathMapAfterCentralAxis_surjective pi hpi S)
    (wreathMapAfterCentralAxis_central_kernel pi S)
    (wreathMapAfterCentralAxis_kernel_card_le pi S hkernel)

/-- The full two-step central comparison of a ternary section with `QStar`.
The outer step is the literal quotient by the first central kernel axis. -/
noncomputable def centralSeriesWreathComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4) :
    CentralBinaryRecursiveComparison QStarGroup R (R ⧸ S.C) := by
  let D := firstCentralWreathComparison pi hpi S hkernel
  let Dprod := firstCentralWreathProductComparison pi hpi S hkernel
  refine
    { projection := QuotientGroup.mk' S.C
      projection_surjective := QuotientGroup.mk'_surjective S.C
      central_kernel := ?_
      kernel_card_le_two := ?_
      baseCoefficient := D.coefficient
      productCoefficient := Dprod.coefficient
      base_complete_bound := D.completeQuotientWeight_le
      product_complete_bound := Dprod.completeQuotientWeight_le }
  · intro z hz x
    have hzC : z ∈ S.C := by
      simpa only [QuotientGroup.ker_mk'] using hz
    exact Subgroup.mem_center_iff.mp (S.C_le_center hzC) x
  · rw [QuotientGroup.ker_mk', S.C_card]

/-- Complete comparison of every normal quotient of the ternary section
with the literal faithful degree-ten `QStar` action. -/
theorem centralSeriesWreath_completeQuotientWeight_le
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      ((centralSeriesWreathComparison pi hpi S hkernel).coefficient : ℝ) *
        completeQuotientWeight (R := QStar) J := by
  let D := centralSeriesWreathComparison pi hpi S hkernel
  calc
    completeQuotientWeight (R := R) J ≤
        (D.coefficient : ℝ) * completeQuotientWeight (R := QStarGroup) J :=
      D.completeQuotientWeight_le J
    _ = (D.coefficient : ℝ) * completeQuotientWeight (R := QStar) J := by
      rw [Non2UnipotentPrefixFiniteMenu.completeQuotientWeight_congr
        qStarEquiv J]

/-- The two central binary layers cost at most `2^200` whenever the whole
section has order at most `2^9`.  The actual sections have order at most
`72 · 4 = 288`, so this leaves substantial room in the final `2^384`
budget. -/
theorem centralSeriesWreath_coefficient_le
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.G)
    (hpi : Function.Surjective pi)
    (S : BinaryNormalKernelCentralSeries R pi.ker)
    (hkernel : Nat.card pi.ker ≤ 4)
    (hR : Nat.card R ≤ 2 ^ 9) :
    (centralSeriesWreathComparison pi hpi S hkernel).coefficient ≤
      2 ^ 200 := by
  let X := R ⧸ S.C
  let D := firstCentralWreathComparison pi hpi S hkernel
  let Dprod := firstCentralWreathProductComparison pi hpi S hkernel
  let O := centralSeriesWreathComparison pi hpi S hkernel
  have hX : Nat.card X ≤ 2 ^ 9 :=
    (Nat.card_le_card_of_surjective
      (QuotientGroup.mk' S.C)
      (QuotientGroup.mk'_surjective S.C)).trans hR
  have hWreath : Nat.card DegreeSixS3Wreath.G ≤ 2 ^ 7 := by
    rw [DegreeSixS3Wreath.card_G]
    norm_num
  have hD : D.coefficient ≤ 2 ^ 89 := by
    apply D.coefficient_le_two_pow_of_card_le_pow 9 7 0 hX hWreath
    · change 1 ≤ 2 ^ 0
      norm_num
    · change 1 ≤ 2 ^ 0
      norm_num
  have hXprod : Nat.card (X × C2) ≤ 2 ^ 10 := by
    rw [Nat.card_prod]
    have hC2 : Nat.card C2 = 2 := by norm_num [C2, Nat.card_zmod]
    rw [hC2]
    calc
      Nat.card X * 2 ≤ 2 ^ 9 * 2 := Nat.mul_le_mul_right 2 hX
      _ = 2 ^ 10 := by norm_num
  have hWreathProd : Nat.card (DegreeSixS3Wreath.G × C2) ≤ 2 ^ 8 := by
    rw [Nat.card_prod, DegreeSixS3Wreath.card_G]
    norm_num [C2, Nat.card_zmod]
  have hDprod : Dprod.coefficient ≤ 2 ^ 109 := by
    apply Dprod.coefficient_le_two_pow_of_card_le_pow
      10 8 0 hXprod hWreathProd
    · change 1 ≤ 2 ^ 0
      norm_num
    · change 1 ≤ 2 ^ 0
      norm_num
  apply O.coefficient_le_two_pow_of_card_le_pow 9 9 109 hR hX
  · change D.coefficient ≤ 2 ^ 109
    exact hD.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  · change Dprod.coefficient ≤ 2 ^ 109
    exact hDprod

end DegreeThreeFourBlockTwoSignComparator
end SymmetricSubgroupAsymptotics

end
