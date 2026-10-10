import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignTopFrame
import SymmetricSubgroupAsymptotics.CentralBinaryCompleteQuotientComparison
import SymmetricSubgroupAsymptotics.PrimitiveAffineProjectiveCentralQuotients
import SymmetricSubgroupAsymptotics.BinaryCoverage
import SymmetricSubgroupAsymptotics.NormalOrderTwo
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Central binary series for the two-sign four-block comparison

The two-sign ternary-section argument leaves a normal kernel of order two
or four inside a finite 2-group.  This file records the catalogue-free
group-theoretic reduction used by that argument.

* A nontrivial normal subgroup of order at most four contains a central
  subgroup of order two.
* Its image after quotienting that subgroup is again central.  Thus the
  kernel has a central series with at most two binary factors.
* One top-level central binary epimorphism, together with the two required
  quotients of a fixed comparator, supplies the existing all-normal-axes
  `CentralBinaryCompleteComparison` automatically.

The last construction is the reusable bridge from a central-series step to
the literal `QStar` quotient comparison.  It descends the given extension to
every actual normal quotient; no normal-subgroup catalogue is introduced.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

private abbrev C2 := Multiplicative (ZMod 2)

/-- A central series of length at most two for a small normal subgroup of a
finite 2-group.  The first factor has order two.  The remaining image may be
trivial; if it is nontrivial, it also has order two and is central. -/
structure BinaryNormalKernelCentralSeries
    (G : Type*) [Group G] (K : Subgroup G) where
  C : Subgroup G
  [normalC : C.Normal]
  C_le_K : C ≤ K
  C_card : Nat.card C = 2
  C_le_center : C ≤ Subgroup.center G
  quotientKernel_le_center :
    K.map (QuotientGroup.mk' C) ≤ Subgroup.center (G ⧸ C)

attribute [instance] BinaryNormalKernelCentralSeries.normalC

/-- A central subgroup of order two inside a normal subgroup of order at
most four supplies the whole two-step binary central series.  This version
does not require the ambient group to be a 2-group; it is useful for split
extensions with an odd normal layer which centralizes the selected binary
axis. -/
noncomputable def binaryNormalKernelCentralSeries_of_central_order_two
    {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal]
    (C : Subgroup G) [C.Normal]
    (hCleK : C ≤ K)
    (hCcard : Nat.card C = 2)
    (hCcenter : C ≤ Subgroup.center G)
    (hKcard : Nat.card K ≤ 4) :
    BinaryNormalKernelCentralSeries G K := by
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  let L : Subgroup (G ⧸ C) := K.map q
  letI : L.Normal :=
    Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  let f : K →* L := q.subgroupMap K
  have hf : Function.Surjective f := q.subgroupMap_surjective K
  have hker : f.ker = C.subgroupOf K := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  have hkerCard : Nat.card f.ker = 2 := by
    rw [hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleK).toEquiv,
      hCcard]
  have hcard := f.ker.card_mul_index
  rw [Subgroup.index_ker, f.range_eq_top_of_surjective hf,
    Nat.card_congr Subgroup.topEquiv.toEquiv, hkerCard] at hcard
  have hLcard : Nat.card L ≤ 2 := by omega
  have hLcenter : L ≤ Subgroup.center (G ⧸ C) := by
    by_cases hsmall : Nat.card L ≤ 1
    · rw [L.eq_bot_of_card_le hsmall]
      exact bot_le
    · exact NormalOrderTwo.le_center L (by omega)
  exact
    { C := C
      normalC := inferInstance
      C_le_K := hCleK
      C_card := hCcard
      C_le_center := hCcenter
      quotientKernel_le_center := hLcenter }

/-- A nontrivial normal subgroup of order at most four in a finite 2-group
has a central series with at most two binary factors.

The first central element is supplied by the finite p-group center theorem.
After dividing by its order-two subgroup, the image of `K` has order at most
two.  Its normality then makes it central in the quotient. -/
noncomputable def binaryNormalKernelCentralSeries_of_card_le_four
    {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G)
    (K : Subgroup G) [K.Normal]
    (hKne : K ≠ ⊥) (hKcard : Nat.card K ≤ 4) :
    BinaryNormalKernelCentralSeries G K := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let hex := pGroup_normal_contains_central_prime hG K hKne
  let z : G := Classical.choose hex
  have hzK : z ∈ K := (Classical.choose_spec hex).1
  have hzcenter : z ∈ Subgroup.center G :=
    (Classical.choose_spec hex).2.1
  have hzorder : orderOf z = 2 := (Classical.choose_spec hex).2.2
  let C : Subgroup G := Subgroup.zpowers z
  have hCleK : C ≤ K := Subgroup.zpowers_le.mpr hzK
  have hCcard : Nat.card C = 2 := by
    change Nat.card (Subgroup.zpowers z) = 2
    rw [Nat.card_zpowers, hzorder]
  have hCcenter : C ≤ Subgroup.center G :=
    Subgroup.zpowers_le.mpr hzcenter
  have hCnormal : C.Normal := by
    constructor
    intro x hx g
    have hxc := hCcenter hx
    simpa [Subgroup.mem_center_iff.mp hxc g, mul_assoc] using hx
  letI : C.Normal := hCnormal
  letI : C.Normal := hCnormal
  exact binaryNormalKernelCentralSeries_of_central_order_two
    K C hCleK hCcard hCcenter hKcard

/-- Top-level data for applying the central-binary quotient comparison to
all literal normal quotients of one group.  The two maps out of `Q` are the
only comparator-specific input: one onto the projective target and one onto
that target times a binary factor. -/
structure CentralBinaryGlobalComparison
    (Q R : Type*) (A : Type)
    [Group Q] [Finite Q] [Group R] [Finite R] [Group A] [Finite A] where
  projection : R →* A
  projection_surjective : Function.Surjective projection
  central_kernel : ∀ z ∈ projection.ker, ∀ x : R, z * x = x * z
  kernel_card_le_two : Nat.card projection.ker ≤ 2
  baseQuotient : Q →* A
  baseQuotient_surjective : Function.Surjective baseQuotient
  productQuotient : Q →* (A × C2)
  productQuotient_surjective : Function.Surjective productQuotient

namespace CentralBinaryGlobalComparison

variable {Q R : Type*} {A : Type}
  [Group Q] [Finite Q] [Group R] [Finite R] [Group A] [Finite A]
  (D : CentralBinaryGlobalComparison Q R A)

/-- Descend one central binary extension through every literal normal
quotient.  Projective centrality and the binary kernel bound survive the
descent, while postcomposing the two fixed comparator quotients supplies the
required quotient maps at every axis. -/
noncomputable def toCompleteComparison :
    CentralBinaryCompleteComparison Q R where
  quotient := fun M => by
    letI : M.1.Normal := M.2
    let image := ProjectiveCentralQuotient.normalImage
      D.projection D.projection_surjective M
    letI : image.1.Normal := image.2
    let projectionM : (R ⧸ M.1) →* (A ⧸ image.1) :=
      ProjectiveCentralQuotient.map
        D.projection D.projection_surjective M
    let kernelEmbedding := binaryEmbeddingOfCardLETwo projectionM.ker
      ((ProjectiveCentralQuotient.card_kernel_le
          D.projection D.projection_surjective M).trans
        D.kernel_card_le_two)
    exact
      { A := A ⧸ image.1
        projection := projectionM
        projection_surjective :=
          ProjectiveCentralQuotient.map_surjective
            D.projection D.projection_surjective M
        central_kernel :=
          ProjectiveCentralQuotient.central_kernel
            D.projection D.projection_surjective M D.central_kernel
        kernelCharacter := kernelEmbedding.1
        kernelCharacter_injective := kernelEmbedding.2
        baseQuotient := (QuotientGroup.mk' image.1).comp D.baseQuotient
        baseQuotient_surjective :=
          (QuotientGroup.mk'_surjective image.1).comp
            D.baseQuotient_surjective
        productQuotient :=
          ((QuotientGroup.mk' image.1).prodMap (MonoidHom.id C2)).comp
            D.productQuotient
        productQuotient_surjective :=
          ((QuotientGroup.mk'_surjective image.1).prodMap
            Function.surjective_id).comp D.productQuotient_surjective }

/-- Complete quotient weight comparison obtained directly from the global
central-binary extension data. -/
theorem completeQuotientWeight_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      ((D.toCompleteComparison).coefficient : ℝ) *
        completeQuotientWeight (R := Q) J :=
  D.toCompleteComparison.completeQuotientWeight_le J

end CentralBinaryGlobalComparison

namespace DegreeThreeFourBlockTwoSignComparator

/-- The fixed `QStar` product has the two quotient maps needed to control a
central binary extension of the literal `D8` target. -/
noncomputable def centralD8GlobalComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* DegreeSixS3Wreath.D8)
    (hpi : Function.Surjective pi)
    (hcentral : ∀ z ∈ pi.ker, ∀ x : R, z * x = x * z)
    (hkernel : Nat.card pi.ker ≤ 2) :
    CentralBinaryGlobalComparison QStarGroup R DegreeSixS3Wreath.D8 where
  projection := pi
  projection_surjective := hpi
  central_kernel := hcentral
  kernel_card_le_two := hkernel
  baseQuotient := DegreeSixS3Wreath.projection.comp qStarToWreath
  baseQuotient_surjective :=
    DegreeSixS3Wreath.projection_surjective.comp qStarToWreath_surjective
  productQuotient :=
    (DegreeSixS3Wreath.projection.prodMap (MonoidHom.id C2)).comp
      qStarToWreathC2
  productQuotient_surjective :=
    (DegreeSixS3Wreath.projection_surjective.prodMap
      Function.surjective_id).comp qStarToWreathC2_surjective

/-- The second auxiliary binary factor in `QStar` supplies the analogous
comparison for a central binary extension of `D8 × C2`.  This is the second
step used by a two-factor central series. -/
noncomputable def centralD8C2GlobalComparison
    {R : Type*} [Group R] [Finite R]
    (pi : R →* (DegreeSixS3Wreath.D8 × C2))
    (hpi : Function.Surjective pi)
    (hcentral : ∀ z ∈ pi.ker, ∀ x : R, z * x = x * z)
    (hkernel : Nat.card pi.ker ≤ 2) :
    CentralBinaryGlobalComparison QStarGroup R
      (DegreeSixS3Wreath.D8 × C2) where
  projection := pi
  projection_surjective := hpi
  central_kernel := hcentral
  kernel_card_le_two := hkernel
  baseQuotient :=
    (DegreeSixS3Wreath.projection.prodMap (MonoidHom.id C2)).comp
      qStarToWreathC2
  baseQuotient_surjective :=
    (DegreeSixS3Wreath.projection_surjective.prodMap
      Function.surjective_id).comp qStarToWreathC2_surjective
  productQuotient := qStarToD8C2C2
  productQuotient_surjective := qStarToD8C2C2_surjective

/-- Convert a complete comparison against the abstract product underlying
`QStar` to the literal faithful degree-ten permutation comparator. -/
theorem completeQuotientWeight_le_literalQStar_of_global
    {R A : Type} [Group R] [Finite R] [Group A] [Finite A]
    (D : CentralBinaryGlobalComparison QStarGroup R A)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      ((D.toCompleteComparison).coefficient : ℝ) *
        completeQuotientWeight (R := QStar) J := by
  calc
    completeQuotientWeight (R := R) J ≤
        ((D.toCompleteComparison).coefficient : ℝ) *
          completeQuotientWeight (R := QStarGroup) J :=
      D.completeQuotientWeight_le J
    _ = ((D.toCompleteComparison).coefficient : ℝ) *
          completeQuotientWeight (R := QStar) J := by
      rw [Non2UnipotentPrefixFiniteMenu.completeQuotientWeight_congr
        qStarEquiv J]

end DegreeThreeFourBlockTwoSignComparator
end SymmetricSubgroupAsymptotics

end
