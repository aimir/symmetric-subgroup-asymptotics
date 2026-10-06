import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockPairPackage
import SymmetricSubgroupAsymptotics.PrimitiveAffineBlockCoordinateSeparation

/-!
# Full literal translation coordinates in the binary four-block quotient

For an actual degree-three affine component, a binary signed quotient forces
the global translation intersection to be nontrivial: the original
transitive degree-twelve group has order divisible by three, whereas the
quotient has two-power order.  Transitivity of the actual block top then
transports a nonzero translation coordinate to every block.  Each local
translation group has prime order three, so every coordinate projection is
onto.

The conclusion is coordinatewise fullness of the *correlated* literal
translation submodule.  It does not replace that submodule by the direct
product.  The separate distinct-sign projector is what can turn this
coordinatewise statement into equality with `F₃⁴` in the four-isotype
branch.
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

omit [Nontrivial block.Fibre] in
/-- Conjugation transports one literal raw translation coordinate to the
corresponding block coordinate.  This is the actual wreath identity before
the local kernel is changed into vector-space coordinates. -/
theorem rawTranslationCoordinate_conjugation
    (a : preE7NonPairAction w U) (e : E block P) (i : block.Points) :
    PermutationalWreathProduct.Compression.kernelCoordinate
        (ambientEmbedding block) (localMap block P)
        ((ambientEmbedding block a).right • i)
        (MulAut.conjNormal a e) =
      MulAut.conjNormal
        ((ambientEmbedding block a).left
          ((ambientEmbedding block a).right • i))
        (PermutationalWreathProduct.Compression.kernelCoordinate
          (ambientEmbedding block) (localMap block P) i e) := by
  apply Subtype.ext
  change (ambientEmbedding block (a * e.1 * a⁻¹)).left
      ((ambientEmbedding block a).right • i) =
    (ambientEmbedding block a).left
        ((ambientEmbedding block a).right • i) *
      (ambientEmbedding block e.1).left i *
      ((ambientEmbedding block a).left
        ((ambientEmbedding block a).right • i))⁻¹
  rw [map_mul, map_mul, map_inv]
  have heright : (ambientEmbedding block e.1).right = 1 :=
    ((PermutationalWreathProduct.mem_mapBase_ker_iff
      (localMap block P) (ambientEmbedding block e.1)).mp e.2).1
  simp [PermutationalWreathProduct.mul_left,
    PermutationalWreathProduct.mul_right,
    PermutationalWreathProduct.inv_left, heright, smul_smul]

/-- The literal translation intersection cannot vanish when the degree-eight
signed quotient is binary. -/
theorem degreeThreeFourBlock_translationIntersection_ne_bot
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    E block P ≠ ⊥ := by
  intro hE
  let C := degreeThreeFourBlockPairChart block P hr hs hcomponent
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hbinary
  have hwidth : w = 12 := by
    calc
      w = Nat.card block.Fibre * Nat.card block.Points := width_eq block
      _ = 12 := by rw [hr, hs]
  have hwdiv : w ∣ Nat.card (preE7NonPairAction w U) := by
    simpa only [Nat.card_fin] using
      (transitive_natCard_dvd_group_natCard
        (B := preE7NonPairAction w U) (X := Fin w) basePoint)
  have hthreeU : 3 ∣ Nat.card (preE7NonPairAction w U) := by
    exact (by rw [hwidth]; norm_num : 3 ∣ w).trans hwdiv
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (E block P)
  have hEcard : Nat.card (E block P) = 1 := by
    rw [hE, Subgroup.card_bot]
  have hquotientCard :
      Nat.card (preE7NonPairAction w U ⧸ E block P) =
        Nat.card (preE7NonPairAction w U) := by
    rw [hEcard, mul_one] at hmul
    exact hmul.symm
  have hthreeAction : 3 ∣ Nat.card C.action := by
    rw [← Nat.card_congr C.sourceEquiv.toEquiv, hquotientCard]
    exact hthreeU
  rw [hn] at hthreeAction
  have hbad : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthreeAction
  norm_num at hbad

/-- Nontriviality of the global translation intersection and transitivity of
the actual top make every literal local translation coordinate onto. -/
theorem degreeThree_translationCoordinate_surjective_of_ne_bot
    (hr : Nat.card block.Fibre = 3)
    (hE : E block P ≠ ⊥)
    (i : block.Points) :
    Function.Surjective (coordinate block P i) := by
  obtain ⟨e, he⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE
  have hexists : ∃ i₀ : block.Points, coordinate block P i₀ e ≠ 1 := by
    by_contra hnone
    simp only [not_exists, not_not] at hnone
    apply he
    apply coordinates_injective block P
    funext j
    simpa only [map_one] using hnone j
  obtain ⟨i₀, hi₀⟩ := hexists
  letI : MulAction.IsPretransitive block.Top block.Points :=
    block.top_pretransitive
  obtain ⟨q, hq⟩ := MulAction.exists_smul_eq block.Top i₀ i
  obtain ⟨a, ha⟩ := block.topMap.rangeRestrict_surjective q
  have hright : (ambientEmbedding block a).right • i₀ = i := by
    change block.topMap.rangeRestrict a • i₀ = i
    rw [ha]
    exact hq
  let e' : E block P := MulAut.conjNormal a e
  have hraw₀ :
      PermutationalWreathProduct.Compression.kernelCoordinate
          (ambientEmbedding block) (localMap block P) i₀ e ≠ 1 := by
    intro hzero
    apply hi₀
    simp only [coordinate, MonoidHom.comp_apply, hzero, map_one]
  have hraw :
      PermutationalWreathProduct.Compression.kernelCoordinate
          (ambientEmbedding block) (localMap block P) i e' ≠ 1 := by
    intro hzero
    have htransport := rawTranslationCoordinate_conjugation block P a e i₀
    rw [hright] at htransport
    have hone : MulAut.conjNormal
        ((ambientEmbedding block a).left i)
        (PermutationalWreathProduct.Compression.kernelCoordinate
          (ambientEmbedding block) (localMap block P) i₀ e) = 1 := by
      rw [← htransport]
      exact hzero
    exact hraw₀ (Subtype.ext ((conj_eq_one_iff).mp
      (congrArg Subtype.val hone)))
  have hcoordinate : coordinate block P i e' ≠ 1 := by
    intro hzero
    apply hraw
    apply (localKernelEquiv block P).symm.injective
    simpa only [coordinate, MonoidHom.comp_apply, map_one] using hzero
  have hrange_ne : (coordinate block P i).range ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    exact ⟨⟨coordinate block P i e', ⟨e', rfl⟩⟩, by
      intro hx
      exact hcoordinate (congrArg Subtype.val hx)⟩
  have hcard : Nat.card (Multiplicative (chart block P).V) = 3 := by
    calc
      Nat.card (Multiplicative (chart block P).V) = Nat.card P.V :=
        Nat.card_congr (chart block P).equiv.symm.toEquiv
      _ = Nat.card block.Fibre := P.card_eq (origin block)
      _ = 3 := hr
  letI : Fact (Nat.card (Multiplicative (chart block P).V)).Prime :=
    ⟨hcard.symm ▸ Nat.prime_three⟩
  have hrange_top : (coordinate block P i).range = ⊤ :=
    (coordinate block P i).range.eq_bot_or_eq_top_of_prime_card.resolve_left
      hrange_ne
  exact MonoidHom.range_eq_top.mp hrange_top

/-- Every original block coordinate of the correlated translation submodule
is onto in the binary four-block branch.  No assertion of independence is
made. -/
theorem degreeThreeFourBlock_translationSubmodule_fullCoordinates
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action) :
    ∀ i : block.Points, Function.Surjective (coordinate block P i) := by
  have hE := degreeThreeFourBlock_translationIntersection_ne_bot
    block P hr hs hcomponent hbinary
  intro i
  exact degreeThree_translationCoordinate_surjective_of_ne_bot
    block P hr hE i

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
