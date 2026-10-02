import SymmetricSubgroupAsymptotics.Non2PreE7SaprimExceptionalOdd
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTemplate
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineProjectiveCentralQuotients

/-!
# Central cyclic lifts in degree twenty-five

Let `X` be a literal quotient of a soluble subgroup of `GL₂(5)`.  Its scalar
kernel is cyclic of order dividing four, and its projective image has order at
most twenty-four.  This file proves the counting consequence rather than
assuming it: central-lift fibres inject into `C₄` characters of the source,
Kovács--Praeger bounds those characters through the source abelianization,
and ordinary generator counting handles the projective image.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

private abbrev C4 := Multiplicative (ZMod 4)
private abbrev C2 := Multiplicative (ZMod 2)

private def binaryIntoFour : C2 →* C4 where
  toFun x := Multiplicative.ofAdd (2 * (x.toAdd.val : ZMod 4))
  map_one' := by decide
  map_mul' := by decide +kernel

private theorem binaryIntoFour_injective :
    Function.Injective binaryIntoFour := by decide +kernel

/-- A finite cyclic group whose order divides four embeds in `C₄`.
This is the exact closure property needed after a central scalar kernel is
passed to a normal quotient. -/
noncomputable def cyclicFourEmbeddingOfCardDvdFour
    (K : Type*) [Group K] [Finite K]
    (hcyclic : IsCyclic K) (hcard : Nat.card K ∣ 4) :
    {chi : K →* C4 // Function.Injective chi} :=
  Classical.choice (show Nonempty {chi : K →* C4 // Function.Injective chi} from by
    letI : IsCyclic K := hcyclic
    have hpos : 0 < Nat.card K := Nat.card_pos
    have hle : Nat.card K ≤ 4 := Nat.le_of_dvd (by norm_num) hcard
    have hne3 : Nat.card K ≠ 3 := by
      intro h3
      rw [h3] at hcard
      norm_num at hcard
    have hcases : Nat.card K = 1 ∨ Nat.card K = 2 ∨ Nat.card K = 4 := by
      omega
    rcases hcases with h1 | h2 | h4
    · letI : Subsingleton K := (Nat.card_eq_one_iff_unique.mp h1).1
      exact ⟨⟨1, fun _ _ _ => Subsingleton.elim _ _⟩⟩
    · let e : K ≃* C2 := mulEquivOfCyclicCardEq (by simp [h2])
      exact ⟨⟨binaryIntoFour.comp e.toMonoidHom,
        binaryIntoFour_injective.comp e.injective⟩⟩
    · let e : K ≃* C4 := mulEquivOfCyclicCardEq (by simp [h4])
      exact ⟨⟨e.toMonoidHom, e.injective⟩⟩)

/-- Structural information on one literal quotient.  These fields are the
finite-group content of the scalar/projective reduction; there is no counting
inequality in the datum. -/
structure CentralFourQuotientDatum
    (X : Type*) [Group X] [Finite X] where
  P : Type
  [groupP : Group P]
  [finiteP : Finite P]
  projection : X →* P
  projection_surjective : Function.Surjective projection
  central_kernel : ∀ z ∈ projection.ker, ∀ x : X, z * x = x * z
  kernelCharacter : projection.ker →* C4
  kernelCharacter_injective : Function.Injective kernelCharacter
  projective_order_le : Nat.card P ≤ 24

attribute [instance] CentralFourQuotientDatum.groupP
  CentralFourQuotientDatum.finiteP

namespace CentralFourQuotientDatum

variable {X : Type*} [Group X] [Finite X]
  (D : CentralFourQuotientDatum X)

include D in
/-- The scalar/projective datum already bounds the order of its source.
The kernel embeds in `C₄`, while surjectivity identifies the index of the
kernel with the order of the projective image. -/
theorem source_card_le_96 : Nat.card X ≤ 96 := by
  have hker : Nat.card D.projection.ker ≤ 4 := by
    calc
      Nat.card D.projection.ker ≤ Nat.card C4 :=
        Nat.card_le_card_of_injective D.kernelCharacter
          D.kernelCharacter_injective
      _ = 4 := by simp [C4]
  have hrange : Nat.card D.projection.range = Nat.card D.P := by
    rw [MonoidHom.range_eq_top.mpr D.projection_surjective]
    simp
  calc
    Nat.card X = Nat.card D.projection.ker * D.projection.ker.index :=
      D.projection.ker.card_mul_index.symm
    _ = Nat.card D.projection.ker * Nat.card D.projection.range := by
      rw [Subgroup.index_ker]
    _ = Nat.card D.projection.ker * Nat.card D.P := by rw [hrange]
    _ ≤ 4 * 24 := Nat.mul_le_mul hker D.projective_order_le
    _ = 96 := by norm_num

theorem kernel_hom_card_le_cyclicFour {J : Type*} [Group J] [Finite J] :
    Nat.card (J →* D.projection.ker) ≤ Nat.card (J →* C4) := by
  letI : Finite (J →* D.projection.ker) :=
    Finite.of_injective (fun f : J →* D.projection.ker => (f : J → D.projection.ker))
      DFunLike.coe_injective
  letI : Finite (J →* C4) :=
    Finite.of_injective (fun f : J →* C4 => (f : J → C4)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective
    (fun f : J →* D.projection.ker => D.kernelCharacter.comp f)
    (fun f g h => MonoidHom.ext fun x => D.kernelCharacter_injective
      (DFunLike.congr_fun h x))

include D in
/-- The central scalar/projective datum descends to every normal quotient.
The induced scalar kernel is a quotient of the original cyclic subgroup of
`C₄`, hence is cyclic of order dividing four and embeds back into `C₄`. -/
noncomputable def quotientDatum
    (M : {M : Subgroup X // M.Normal}) :
    CentralFourQuotientDatum (X ⧸ M.1) := by
  let pi := D.projection
  let hpi := D.projection_surjective
  let qpi := ProjectiveCentralQuotient.map pi hpi M
  let kmap := ProjectiveCentralQuotient.kernelMap pi hpi M
  let rangeEquiv : pi.ker ≃* D.kernelCharacter.range :=
    MulEquiv.ofBijective D.kernelCharacter.rangeRestrict
      ⟨fun a b h => D.kernelCharacter_injective (congrArg Subtype.val h),
        D.kernelCharacter.rangeRestrict_surjective⟩
  have hkernelCyclic : IsCyclic pi.ker :=
    (MulEquiv.isCyclic rangeEquiv).mpr inferInstance
  letI : IsCyclic pi.ker := hkernelCyclic
  have hinducedCyclic : IsCyclic qpi.ker :=
    isCyclic_of_surjective kmap
      (ProjectiveCentralQuotient.kernelMap_surjective pi hpi M)
  have horiginalDvd : Nat.card pi.ker ∣ 4 := by
    rw [Nat.card_congr rangeEquiv.toEquiv]
    simpa [C4] using D.kernelCharacter.range.card_subgroup_dvd_card
  have hinducedDvd : Nat.card qpi.ker ∣ 4 :=
    (Subgroup.card_dvd_of_surjective kmap
      (ProjectiveCentralQuotient.kernelMap_surjective pi hpi M)).trans
        horiginalDvd
  let chi := cyclicFourEmbeddingOfCardDvdFour qpi.ker
    hinducedCyclic hinducedDvd
  exact
    { P := D.P ⧸ (ProjectiveCentralQuotient.normalImage pi hpi M).1
      projection := qpi
      projection_surjective :=
        ProjectiveCentralQuotient.map_surjective pi hpi M
      central_kernel :=
        ProjectiveCentralQuotient.central_kernel pi hpi M D.central_kernel
      kernelCharacter := chi.1
      kernelCharacter_injective := chi.2
      projective_order_le := by
        exact (Nat.card_le_card_of_surjective
          (QuotientGroup.mk'
            (ProjectiveCentralQuotient.normalImage pi hpi M).1)
          (QuotientGroup.mk'_surjective _)).trans D.projective_order_le }

private theorem three_rpow_eq_two {b : ℕ} :
    (3 : ℝ) ^ ((b : ℝ) / 3) =
      (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  rw [show (Real.logb 2 3 / 3) * (b : ℝ) =
      Real.logb 2 3 * ((b : ℝ) / 3) by ring,
    Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]

/-- The central fibre is bounded by the published abelianization theorem.
The only group-specific step is its faithful embedding in `C₄`. -/
theorem kernel_hom_bound
    (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (J →* D.projection.ker) : ℝ) ≤
      (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  calc
    (Nat.card (J →* D.projection.ker) : ℝ) ≤
        Nat.card (J →* C4) := by
      exact_mod_cast D.kernel_hom_card_le_cyclicFour (J := J)
    _ ≤ Nat.card (Abelianization J) := by
      exact_mod_cast cyclicCharacter_card_le_abelianization J 4
    _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := hKP b J
    _ = _ := three_rpow_eq_two

include D in
/-- One literal central quotient has the claimed pure exponential row. -/
theorem epi_card_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J X) : ℝ) ≤
      24 * (2 : ℝ) ^
        (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
  have hlift := epi_card_le_centralLift (J := J) D.projection
    D.projection_surjective D.central_kernel
  have hproj := Non2UnipotentPrefixFiniteMenu.PreE7SaprimOddLargeAffineSource.epi_le_orderCeiling
    hgen J (q := 24) (by norm_num) D.projective_order_le
  have hker := D.kernel_hom_bound hKP J
  calc
    (Nat.card (GroupEpimorphism J X) : ℝ) ≤
        (Nat.card (GroupEpimorphism J D.P) : ℝ) *
          Nat.card (J →* D.projection.ker) := by exact_mod_cast hlift
    _ ≤ (24 * (2 : ℝ) ^ ((Real.logb 2 24 / 2) * b)) *
          (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) :=
      mul_le_mul hproj hker (Nat.cast_nonneg _) (by positivity)
    _ = 24 * (2 : ℝ) ^
          (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num)]
      unfold Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope
      congr 3
      ring

end CentralFourQuotientDatum

/-- Structural scalar/projective data on all normal quotients of one fixed
degree-twenty-five complement. -/
structure DegreeTwentyFiveCentralFourModel
    (R : Type*) [Group R] [Finite R] where
  quotient : ∀ M : {M : Subgroup R // M.Normal},
    CentralFourQuotientDatum (R ⧸ M.1)

namespace DegreeTwentyFiveCentralFourModel

variable {R : Type*} [Group R] [Finite R]
  (D : DegreeTwentyFiveCentralFourModel R)

/-- A single top-level scalar/projective datum supplies the former
all-normal-quotients model.  No separate quotient-by-quotient catalogue is
needed. -/
noncomputable def ofTopDatum (D : CentralFourQuotientDatum R) :
    DegreeTwentyFiveCentralFourModel R where
  quotient M := CentralFourQuotientDatum.quotientDatum D M

def coefficient (_D : DegreeTwentyFiveCentralFourModel R) : ℝ :=
  24 * Nat.card {M : Subgroup R // M.Normal}

include D in
/-- The bottom quotient of the all-quotients model is the original group,
so the scalar/projective model itself implies the order ceiling used by the
numerical source. -/
theorem source_card_le_96 : Nat.card R ≤ 96 := by
  let M : {M : Subgroup R // M.Normal} := ⟨⊥, inferInstance⟩
  have hquot := (D.quotient M).source_card_le_96
  rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv] at hquot
  exact hquot

theorem coefficient_nonneg : 0 ≤ D.coefficient := by
  unfold coefficient
  positivity

/-- The coefficient is bounded solely from the published order ceiling on
the linear complement.  As in degree nine, the finite subgroup catalogue
supplies structural scalar/projective data; this numerical consequence is
proved here. -/
theorem coefficient_le (hR : Nat.card R ≤ 96) : D.coefficient ≤ 2 ^ 54 := by
  have hR128 : Nat.card R ≤ 2 ^ 7 := hR.trans (by norm_num)
  have hnormal :
      Nat.card {M : Subgroup R // M.Normal} ≤ 2 ^ 49 := by
    simpa using normalSubgroup_card_le_two_pow_sq 7 hR128
  have hnat :
      24 * Nat.card {M : Subgroup R // M.Normal} ≤ 2 ^ 54 := by
    calc
      24 * Nat.card {M : Subgroup R // M.Normal} ≤ 24 * 2 ^ 49 :=
        Nat.mul_le_mul_left 24 hnormal
      _ ≤ 2 ^ 54 := by norm_num
  unfold coefficient
  exact_mod_cast hnat

/-- Summing the proved per-quotient row gives the complete central-`C₄`
bound, with no normal stratum discarded. -/
theorem complete_bound
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      D.coefficient * (2 : ℝ) ^
        (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
  unfold completeQuotientWeight completeQuotientCount coefficient
  push_cast
  calc
    (∑ M : {M : Subgroup R // M.Normal},
        (Nat.card (GroupEpimorphism J (R ⧸ M.1)) : ℝ)) ≤
      ∑ _M : {M : Subgroup R // M.Normal},
        24 * (2 : ℝ) ^
          (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
      apply Finset.sum_le_sum
      intro M _
      exact (D.quotient M).epi_card_le hgen hKP J
    _ = (24 * Nat.card {M : Subgroup R // M.Normal} : ℝ) *
          (2 : ℝ) ^
            (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Constructor for the numerical source's former counting input. -/
noncomputable def toBound
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    Non2UnipotentPrefixFiniteMenu.PreE7DegreeTwentyFiveCentralFourBound R where
  coefficient := D.coefficient
  coefficient_nonneg := D.coefficient_nonneg
  complete_bound := D.complete_bound hgen hKP

end DegreeTwentyFiveCentralFourModel

end SymmetricSubgroupAsymptotics

end
