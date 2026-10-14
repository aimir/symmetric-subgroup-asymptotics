import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10NormalizerPrefix
import SymmetricSubgroupAsymptotics.TernarySemiregularS3QuotientAnchor

/-!
# The original row-10 group is binary-by-S₃ with semiregular cubic elements

Every map is built from the supplied original pair frame and its literal
top equivalence. The order formula and the original 24-point geometry
therefore apply to every original normal quotient, without selecting an
independent quotient model or adding a rank or module certificate.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10OriginalGeometry

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoTwelveRow10BinaryQuotientPilot
open BinaryPairTernaryNormalizerPrefix

variable {p : PreE7PairActionClass 12}
  (R : DegreeTwoPairTopRealization DegreeTwoTwelvePairFiniteCatalogue.row10Interface p)

/-- The actual original group maps onto the literal row-10 top. -/
def topMap : preE7PairAction 12 p →* Top :=
  R.topEquiv.symm.toMonoidHom.comp R.frame.top.rangeRestrict

theorem topMap_surjective : Function.Surjective (topMap R) :=
  R.topEquiv.symm.surjective.comp R.frame.top.rangeRestrict_surjective

theorem topMap_ker : (topMap R).ker = R.frame.top.ker := by
  ext g
  change R.topEquiv.symm (R.frame.top.rangeRestrict g) = 1 ↔ R.frame.top g = 1
  rw [R.topEquiv.symm.map_eq_one_iff]
  constructor
  · exact fun h ↦ congrArg Subtype.val h
  · exact fun h ↦ Subtype.ext h

theorem topMap_kernel_isPGroup : IsPGroup 2 (topMap R).ker := by
  rw [topMap_ker]
  exact R.frame.kernel_isPGroup

/-- The checked chart transports this same map into `C₂² × S₃`. -/
def modelMap : preE7PairAction 12 p →* Model :=
  modelEquiv.symm.toMonoidHom.comp (topMap R)

theorem modelMap_surjective : Function.Surjective (modelMap R) :=
  modelEquiv.symm.surjective.comp (topMap_surjective R)

theorem modelMap_kernel_isPGroup : IsPGroup 2 (modelMap R).ker := by
  have heq : (modelMap R).ker = (topMap R).ker := by
    ext g
    change modelEquiv.symm (topMap R g) = 1 ↔ topMap R g = 1
    exact modelEquiv.symm.map_eq_one_iff
  rw [heq]
  exact topMap_kernel_isPGroup R

def modelProjection : Model →* Equiv.Perm (Fin 3) :=
  MonoidHom.snd Translation (Equiv.Perm (Fin 3))

theorem modelProjection_surjective : Function.Surjective modelProjection :=
  fun s ↦ ⟨(1, s), rfl⟩

private theorem model_binary_kernel_square (g : Model) (hg : g.2 = 1) :
    g ^ 2 = 1 := by
  decide +kernel +revert

theorem modelProjection_kernel_isPGroup : IsPGroup 2 modelProjection.ker := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  change (g : Model) ^ (2 ^ 1) = 1
  exact model_binary_kernel_square g g.property

/-- The actual original map to `S₃`; its binary kernel includes the pair
kernel and the two translation coordinates in the literal top. -/
def symmetricThreeMap : preE7PairAction 12 p →* Equiv.Perm (Fin 3) :=
  modelProjection.comp (modelMap R)

theorem symmetricThreeMap_surjective : Function.Surjective (symmetricThreeMap R) :=
  modelProjection_surjective.comp (modelMap_surjective R)

theorem symmetricThreeMap_kernel_isPGroup :
    IsPGroup 2 (symmetricThreeMap R).ker :=
  modelProjection_kernel_isPGroup.comap_of_ker_isPGroup
    (modelMap R) (modelMap_kernel_isPGroup R)

include R in
/-- The source order has exactly one ternary factor. The binary exponent
is obtained from the actual pair kernel. -/
theorem original_card : ∃ a : ℕ, Nat.card (preE7PairAction 12 p) = 2 ^ a * 3 := by
  obtain ⟨a, ha⟩ := (topMap_kernel_isPGroup R).exists_card_eq
  have hi : (topMap R).ker.index = Nat.card Top := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (topMap_surjective R),
      Subgroup.card_top]
  have hc : Nat.card (preE7PairAction 12 p) =
      Nat.card (topMap R).ker * Nat.card Top := by
    rw [← hi]
    exact (topMap R).ker.card_mul_index.symm
  refine ⟨a + 3, ?_⟩
  rw [hc, ha, top_card, pow_add]
  ring

theorem topMap_perm (g : preE7PairAction 12 p) :
    ((topMap R g : Top) : Equiv.Perm (Fin 12)) = R.frame.top g := by
  calc
    ((topMap R g : Top) : Equiv.Perm (Fin 12)) =
        ((R.topEquiv (topMap R g) : R.frame.top.range) : Equiv.Perm (Fin 12)) :=
      (realization_topEquiv_perm_eq R (topMap R g)).symm
    _ = R.frame.top g := by
      change ((R.topEquiv (R.topEquiv.symm (R.frame.top.rangeRestrict g)) :
        R.frame.top.range) : Equiv.Perm (Fin 12)) = R.frame.top g
      exact congrArg (fun t : R.frame.top.range ↦ (t : Equiv.Perm (Fin 12)))
        (R.topEquiv.apply_symm_apply (R.frame.top.rangeRestrict g))

include R in
/-- Nonidentity cubic elements are fixed-point-free on the original
twenty-four points, not just on the twelve pair labels. -/
theorem original_cubic_fixedPointFree :
    ∀ g : preE7PairAction 12 p, g ^ 3 = 1 → g ≠ 1 →
      ∀ x : Fin 24, g • x ≠ x := by
  apply TernaryKernelSylowSemiregular.semiregular_of_binary_kernel_top
    (topMap R) (topMap_kernel_isPGroup R)
    (fun x ↦ (R.frame.frame.symm x).1) ?_
    PrimitiveAffineDegreeTwoTwelveRow10NormalizerPrefix.literalTopCertificate.cubic_fixedPointFree
  intro g x
  obtain ⟨v, rfl⟩ := R.frame.frame.surjective x
  change (R.frame.frame.symm ((g : Equiv.Perm (Fin 24)) (R.frame.frame v))).1 =
    ((topMap R g : Top) : Equiv.Perm (Fin 12))
      (R.frame.frame.symm (R.frame.frame v)).1
  rw [topMap_perm, R.frame.intertwine, R.frame.frame.symm_apply_apply]

/-- The nonbinary branch retains the displayed original quotient `U/N`.
All group-theoretic premises of the generic anchor are discharged. -/
noncomputable def nonbinary_quotient_anchor
    (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hQ : ¬ IsPGroup 2 (preE7PairAction 12 p ⧸ N.1)) :
    DegreeTwoPairRelativeKernelAnchor (preE7PairAction 12 p ⧸ N.1)
      (degreeTwoPairOrdinaryRelativeProfile 1 3) := by
  letI : N.1.Normal := N.2
  let orderData := original_card R
  exact ternarySemiregular_s3_nonbinary_normal_quotient_anchor hZmud
    (X := Fin 24) (by simp) orderData.choose_spec
    (original_cubic_fixedPointFree R)
    (symmetricThreeMap R) (symmetricThreeMap_surjective R)
    (symmetricThreeMap_kernel_isPGroup R) N.1 hQ

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow10OriginalGeometry

end
