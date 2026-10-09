import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignProjectiveSeries
import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Literal ternary sections below the four-block translation layer

For every proper normal axis `N` not containing the actual translation
intersection `E`, the arbitrary-normal-quotient construction gives an exact
extension chart on `U / N`.  Its kernel is the literal section

`E / (E ∩ N)`

in the original elementary coordinates, and its acting top is the literal
quotient `U / (E ⊔ N)`.  This file installs those objects for the two-sign
stratification and proves that the retained ternary section is nonzero and
that its acting top is still binary.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev G := preE7NonPairAction w U

private abbrev PairChart
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6) :=
  degreeThreeFourBlockPairChart block P hr hs hcomponent

/-- The original normal subgroup carried by a literal proper two-sign
axis. -/
abbrev degreeThreeFourBlockTwoSignSectionAxis
    (N : TwoSignProperAxis (E block P)) : Subgroup G :=
  (twoSignProperAxis N).1

local instance degreeThreeFourBlockTwoSignSectionAxis_normal
    (N : TwoSignProperAxis (E block P)) :
    (degreeThreeFourBlockTwoSignSectionAxis block P N).Normal :=
  (twoSignProperAxis N).2

/-- The exact quotient module `E / (E ∩ N)` in the elementary translation
coordinates. -/
abbrev DegreeThreeFourBlockTwoSignSectionModule
    (N : TwoSignProperAxis (E block P)) :=
  (elementaryChart block P).originalKernelChart.sectionModule
    (QuotientGroup.mk' (E block P))
    (elementaryChart block P).quotientRepresentation
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

/-- The literal map from the original translation kernel onto its retained
section at `N`. -/
def degreeThreeFourBlockTwoSignSectionMap
    (N : TwoSignProperAxis (E block P)) :
    (QuotientGroup.mk' (E block P)).ker →*
      Multiplicative (DegreeThreeFourBlockTwoSignSectionModule block P N) :=
  (elementaryChart block P).originalKernelChart.sectionMap
    (QuotientGroup.mk' (E block P))
    (elementaryChart block P).quotientRepresentation
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

theorem degreeThreeFourBlockTwoSignSectionMap_surjective
    (N : TwoSignProperAxis (E block P)) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignSectionMap block P N) :=
  (elementaryChart block P).originalKernelChart.sectionMap_surjective
    (QuotientGroup.mk' (E block P))
    (elementaryChart block P).quotientRepresentation
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

/-- The retained section is nonzero because `N` does not contain `E`.
This proof uses the exact kernel theorem for the literal section map. -/
theorem degreeThreeFourBlockTwoSignSectionModule_nontrivial
    (N : TwoSignProperAxis (E block P)) :
    Nontrivial (DegreeThreeFourBlockTwoSignSectionModule block P N) := by
  have hnot : ¬ E block P ≤
      degreeThreeFourBlockTwoSignSectionAxis block P N := N.1.2
  obtain ⟨e, heE, heN⟩ := SetLike.not_le_iff_exists.mp hnot
  let ee : E block P := ⟨e, heE⟩
  let k : (QuotientGroup.mk' (E block P)).ker :=
    (elementaryChart block P).quotientKernelEquiv
      ((elementaryChart block P).equiv ee)
  let y : Multiplicative
      (DegreeThreeFourBlockTwoSignSectionModule block P N) :=
    degreeThreeFourBlockTwoSignSectionMap block P N k
  have hy : y ≠ 1 := by
    intro hy1
    have hk : k ∈ (degreeThreeFourBlockTwoSignSectionMap block P N).ker :=
      MonoidHom.mem_ker.mpr hy1
    have hkN : (k.1 : G) ∈
        degreeThreeFourBlockTwoSignSectionAxis block P N := by
      rw [(elementaryChart block P).originalKernelChart.sectionMap_ker
        (QuotientGroup.mk' (E block P))
        (elementaryChart block P).quotientRepresentation
        (degreeThreeFourBlockTwoSignSectionAxis block P N)] at hk
      exact hk
    apply heN
    have hkval : (k.1 : G) = e := by
      change (((elementaryChart block P).equiv.symm
        ((elementaryChart block P).equiv ee) : E block P) : G) = e
      rw [(elementaryChart block P).equiv.symm_apply_apply]
      rfl
    exact hkval ▸ hkN
  exact ⟨⟨y.toAdd, 0, by
    intro h
    apply hy
    apply Multiplicative.toAdd.injective
    simpa using h⟩⟩

/-- Conjugation on the retained ternary section, factored through the
literal acting top `U / (E ⊔ N)`. -/
abbrev degreeThreeFourBlockTwoSignSectionRepresentation
    (N : TwoSignProperAxis (E block P)) :=
  (elementaryChart block P).originalKernelChart.sectionRepresentation
    (QuotientGroup.mk' (E block P))
    (elementaryChart block P).quotientRepresentation
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

/-- The actual quotient `U / N` maps onto the section's acting top. -/
def degreeThreeFourBlockTwoSignSectionBase
    (N : TwoSignProperAxis (E block P)) :
    G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N →*
      G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N) :=
  (elementaryChart block P).originalKernelChart.base
    (QuotientGroup.mk' (E block P))
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

theorem degreeThreeFourBlockTwoSignSectionBase_surjective
    (N : TwoSignProperAxis (E block P)) :
    Function.Surjective
      (degreeThreeFourBlockTwoSignSectionBase block P N) :=
  (elementaryChart block P).originalKernelChart.base_surjective
    (QuotientGroup.mk' (E block P))
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

/-- Exact elementary extension chart on the original quotient `U / N`. -/
def degreeThreeFourBlockTwoSignSectionQuotientChart
    (N : TwoSignProperAxis (E block P)) :
    OriginalKernelModuleChart
      (degreeThreeFourBlockTwoSignSectionBase block P N)
      (degreeThreeFourBlockTwoSignSectionRepresentation block P N) :=
  (elementaryChart block P).originalKernelChart.quotientChart
    (QuotientGroup.mk' (E block P))
    (elementaryChart block P).quotientRepresentation
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

/-- The kernel of the descended section top is a ternary group. -/
theorem degreeThreeFourBlockTwoSignSectionKernel_isPGroup
    (hr : Nat.card block.Fibre = 3)
    (N : TwoSignProperAxis (E block P)) :
    IsPGroup 3 (degreeThreeFourBlockTwoSignSectionBase block P N).ker := by
  letI : Fact P.p.Prime := (chart block P).primeFact
  have hp : P.p = 3 :=
    (degreeThree_translation_prime_dim block P hr).1
  have hmodule : IsPGroup P.p
      (Multiplicative
        (DegreeThreeFourBlockTwoSignSectionModule block P N)) :=
    ZModModule.isPGroup_multiplicative
  have hkernel : IsPGroup P.p
      (degreeThreeFourBlockTwoSignSectionBase block P N).ker :=
    hmodule.of_equiv
      (degreeThreeFourBlockTwoSignSectionQuotientChart block P N).equiv
  simpa only [hp] using hkernel

/-- The acting top of every literal proper section remains a two-group. -/
theorem degreeThreeFourBlockTwoSignSectionTop_isPGroup
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (N : TwoSignProperAxis (E block P)) :
    IsPGroup 2
      (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N)) := by
  let R := G ⧸ E block P
  let D := (QuotientGroup.mk' (E block P)).ker ⊔
    degreeThreeFourBlockTwoSignSectionAxis block P N
  have hED : E block P ≤ D := by
    dsimp only [D]
    rw [QuotientGroup.ker_mk']
    exact le_sup_left
  let f : R →* G ⧸ D := QuotientGroup.lift (E block P)
    (QuotientGroup.mk' D) hED
  have hf : Function.Surjective f :=
    QuotientGroup.lift_surjective_of_surjective (E block P)
      (QuotientGroup.mk' D)
      (QuotientGroup.mk'_surjective D)
      hED
  change IsPGroup 2 (G ⧸ D)
  exact (degreeThreeFourBlockTwoSign_signedQuotient_isPGroup
    block P hr hs hcomponent hbinary).of_surjective f hf

/-! ## Literal Schur complement of every proper section

The section kernel is ternary and its actual acting top is binary.  Thus
Schur--Zassenhaus applies to the descended extension itself.  Keeping the
chosen complement as a subgroup of the literal quotient is useful for the
next step: the two-sign module action can be compared with the natural
`D8` action without replacing the original extension by a split hypothesis.
-/

/-- Every proper two-sign section splits over its literal ternary kernel.
The complement lives in the actual quotient `U / N`. -/
theorem degreeThreeFourBlockTwoSignSectionComplement_exists
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (PairChart block P hr hs hcomponent).action)
    (N : TwoSignProperAxis (E block P)) :
    ∃ H : Subgroup
        (G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N),
      Subgroup.IsComplement'
        (degreeThreeFourBlockTwoSignSectionBase block P N).ker H := by
  let pi := degreeThreeFourBlockTwoSignSectionBase block P N
  have hkernel : IsPGroup 3 pi.ker :=
    degreeThreeFourBlockTwoSignSectionKernel_isPGroup block P hr N
  have htop : IsPGroup 2
      (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N)) :=
    degreeThreeFourBlockTwoSignSectionTop_isPGroup
      block P hr hs hcomponent hbinary N
  obtain ⟨a, ha⟩ := hkernel.exists_card_eq
  obtain ⟨c, hc⟩ := htop.exists_card_eq
  apply Subgroup.exists_right_complement'_of_coprime
  have hindex : pi.ker.index =
      Nat.card
        (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
          degreeThreeFourBlockTwoSignSectionAxis block P N)) := by
    rw [Subgroup.index_ker, pi.range_eq_top_of_surjective
      (degreeThreeFourBlockTwoSignSectionBase_surjective block P N),
      Nat.card_congr Subgroup.topEquiv.toEquiv]
  rw [ha, hindex, hc]
  exact (Nat.Coprime.pow_left a
    (by decide : Nat.Coprime 3 2)).pow_right c

/-- Restriction of the descended top map to a chosen literal Schur
complement. -/
def degreeThreeFourBlockTwoSignSectionComplementTopHom
    (N : TwoSignProperAxis (E block P))
    (H : Subgroup
      (G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N)) :
    H →*
      G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N) :=
  (degreeThreeFourBlockTwoSignSectionBase block P N).comp H.subtype

/-- A complementary subgroup maps injectively to the literal acting top. -/
theorem degreeThreeFourBlockTwoSignSectionComplementTopHom_injective
    (N : TwoSignProperAxis (E block P))
    (H : Subgroup
      (G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N))
    (hH : Subgroup.IsComplement'
      (degreeThreeFourBlockTwoSignSectionBase block P N).ker H) :
    Function.Injective
      (degreeThreeFourBlockTwoSignSectionComplementTopHom
        block P N H) := by
  intro x y hxy
  have hker : (x : G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N)⁻¹ *
      (y : G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) ∈
        (degreeThreeFourBlockTwoSignSectionBase block P N).ker := by
    apply MonoidHom.mem_ker.mpr
    change
      (degreeThreeFourBlockTwoSignSectionBase block P N
        (x : G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N))⁻¹ *
        degreeThreeFourBlockTwoSignSectionBase block P N
          (y : G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) = 1
    rw [hxy, inv_mul_cancel]
  have hmemH :
      (x : G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N)⁻¹ *
        (y : G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) ∈ H :=
    H.mul_mem (H.inv_mem x.property) y.property
  have hbot :
      (x : G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N)⁻¹ *
        (y : G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N) ∈
          (⊥ : Subgroup
            (G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N)) :=
    hH.disjoint.le_bot ⟨hker, hmemH⟩
  apply Subtype.ext
  exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot)

/-- The chosen complement is exactly the actual acting top, not merely a
subgroup of the same order. -/
noncomputable def degreeThreeFourBlockTwoSignSectionComplementTopEquiv
    (N : TwoSignProperAxis (E block P))
    (H : Subgroup
      (G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N))
    (hH : Subgroup.IsComplement'
      (degreeThreeFourBlockTwoSignSectionBase block P N).ker H) :
    H ≃*
      G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
        degreeThreeFourBlockTwoSignSectionAxis block P N) := by
  let pi := degreeThreeFourBlockTwoSignSectionBase block P N
  let f := degreeThreeFourBlockTwoSignSectionComplementTopHom block P N H
  apply MulEquiv.ofBijective f
  apply (Nat.bijective_iff_injective_and_card f).mpr
  refine ⟨degreeThreeFourBlockTwoSignSectionComplementTopHom_injective
    block P N H hH, ?_⟩
  calc
    Nat.card H = pi.ker.index := hH.card_right
    _ = Nat.card
        (G ⧸ ((QuotientGroup.mk' (E block P)).ker ⊔
          degreeThreeFourBlockTwoSignSectionAxis block P N)) := by
      rw [Subgroup.index_ker, pi.range_eq_top_of_surjective
        (degreeThreeFourBlockTwoSignSectionBase_surjective block P N),
        Nat.card_congr Subgroup.topEquiv.toEquiv]

@[simp] theorem degreeThreeFourBlockTwoSignSectionComplementTopEquiv_apply
    (N : TwoSignProperAxis (E block P))
    (H : Subgroup
      (G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N))
    (hH : Subgroup.IsComplement'
      (degreeThreeFourBlockTwoSignSectionBase block P N).ker H)
    (h : H) :
    degreeThreeFourBlockTwoSignSectionComplementTopEquiv
        block P N H hH h =
      degreeThreeFourBlockTwoSignSectionBase block P N h := rfl

/-- Internal semidirect-product coordinates on the literal section.  The
kernel and complement remain the actual subgroups of `U / N`. -/
noncomputable def degreeThreeFourBlockTwoSignSectionSemidirectEquiv
    (N : TwoSignProperAxis (E block P))
    (H : Subgroup
      (G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N))
    (hH : Subgroup.IsComplement'
      (degreeThreeFourBlockTwoSignSectionBase block P N).ker H) :
    let K := (degreeThreeFourBlockTwoSignSectionBase block P N).ker
    K ⋊[(K.normalizerMonoidHom).comp
        (Subgroup.inclusion (K.normalizer_eq_top ▸ le_top))] H ≃*
      G ⧸ degreeThreeFourBlockTwoSignSectionAxis block P N :=
  SemidirectProduct.mulEquivSubgroup hH

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
