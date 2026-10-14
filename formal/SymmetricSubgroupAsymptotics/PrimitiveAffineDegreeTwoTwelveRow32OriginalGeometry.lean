import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32BinaryChart
import SymmetricSubgroupAsymptotics.BinaryPairTernaryNormalizerPrefix
import SymmetricSubgroupAsymptotics.TernaryOddPartNonbinaryCentralRank
import Mathlib.GroupTheory.Nilpotent

/-!
# Original quotient geometry for row 32

The parameter chart supplies order forty-eight and the fixed-point-free
cubic action on the literal twelve points. The original realization then
supplies its actual 24-point geometry and binary-kernel map to C₃. Every
binary original quotient gets the checked designated-prefix branch;
every nonbinary original quotient has central binary rank at most four.
This file does not assert the remaining nonfixed socle bound.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32OriginalGeometry

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open PrimitiveAffineDegreeTwoTwelveRow32BinaryChart
open BinaryPairTernaryNormalizerPrefix

theorem top_card : Nat.card Top = 48 := by
  rw [← Nat.card_congr modelEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

theorem model_cubic_fixedPointFree
    (g : Model) (hg : g ^ 3 = 1) (hne : g ≠ 1) (x : Fin 12) :
    literalAction g x ≠ x := by
  decide +kernel +revert

theorem literalTopCertificate :
    LiteralTopCertificate DegreeTwoTwelvePairFiniteCatalogue.row32Interface where
  three_dvd := by
    change 3 ∣ Nat.card Top
    rw [top_card]
    decide
  nine_not_dvd := by
    change ¬ 9 ∣ Nat.card Top
    rw [top_card]
    decide
  cubic_fixedPointFree := by
    intro t ht htne i
    obtain ⟨g, rfl⟩ := modelEquiv.surjective t
    have hg : g ^ 3 = 1 := by
      apply modelEquiv.injective
      simpa only [map_pow, map_one] using ht
    have hgne : g ≠ 1 := by
      intro h
      exact htne ((congrArg modelEquiv h).trans modelEquiv.map_one)
    change literalAction g i ≠ i
    exact model_cubic_fixedPointFree g hg hgne i

variable {p : PreE7PairActionClass 12}
  (R : DegreeTwoPairTopRealization DegreeTwoTwelvePairFiniteCatalogue.row32Interface p)

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

def cubicMap : preE7PairAction 12 p →* Cubic := beta.comp (topMap R)

theorem cubicMap_surjective : Function.Surjective (cubicMap R) :=
  beta_surjective.comp (topMap_surjective R)

theorem cubicMap_kernel_isPGroup : IsPGroup 2 (cubicMap R).ker :=
  binaryKernel_isPGroup.comap_of_ker_isPGroup (topMap R) (topMap_kernel_isPGroup R)

include R in
theorem original_solvable : IsSolvable (preE7PairAction 12 p) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Group.IsNilpotent (cubicMap R).ker := (cubicMap_kernel_isPGroup R).isNilpotent
  exact solvable_of_ker_le_range (cubicMap R).ker.subtype (cubicMap R)
    (by rw [Subgroup.range_subtype])

include R in
theorem original_card : ∃ a : ℕ, Nat.card (preE7PairAction 12 p) = 2 ^ a * 3 := by
  obtain ⟨a, ha⟩ := (topMap_kernel_isPGroup R).exists_card_eq
  have hi : (topMap R).ker.index = Nat.card Top := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr (topMap_surjective R),
      Subgroup.card_top]
  have hc : Nat.card (preE7PairAction 12 p) =
      Nat.card (topMap R).ker * Nat.card Top := by
    rw [← hi]
    exact (topMap R).ker.card_mul_index.symm
  refine ⟨a + 4, ?_⟩
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
theorem original_cubic_fixedPointFree :
    ∀ g : preE7PairAction 12 p, g ^ 3 = 1 → g ≠ 1 →
      ∀ x : Fin 24, g • x ≠ x := by
  apply TernaryKernelSylowSemiregular.semiregular_of_binary_kernel_top
    (topMap R) (topMap_kernel_isPGroup R)
    (fun x ↦ (R.frame.frame.symm x).1) ?_ literalTopCertificate.cubic_fixedPointFree
  intro g x
  obtain ⟨v, rfl⟩ := R.frame.frame.surjective x
  change (R.frame.frame.symm ((g : Equiv.Perm (Fin 24)) (R.frame.frame v))).1 =
    ((topMap R g : Top) : Equiv.Perm (Fin 12))
      (R.frame.frame.symm (R.frame.frame v)).1
  rw [topMap_perm, R.frame.intertwine, R.frame.frame.symm_apply_apply]

include R in
theorem binary_quotient_orbitInput
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hQ : IsPGroup 2 (preE7PairAction 12 p ⧸ N.1)) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput
      (preE7PairAction 12 p ⧸ N.1) (degreeTwoPairRelativeProfile 1 0 0 4)) :=
  literal_binary_quotient_orbitInput literalTopCertificate R N hQ

include R in
theorem nonbinary_quotient_central_finrank_le_four
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hQ : ¬ IsPGroup 2 (preE7PairAction 12 p ⧸ N.1)) :
    Module.finrank (ZMod 2)
      (Additive (binaryCentralOmega (preE7PairAction 12 p ⧸ N.1))) ≤ 4 := by
  letI : N.1.Normal := N.2
  obtain ⟨a, ha⟩ := original_card R
  exact ternaryOddPart_nonbinary_normal_quotient_central_finrank_le_four
    (X := Fin 24) (by simp) ha (original_cubic_fixedPointFree R) N.1 hQ

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveRow32OriginalGeometry

end
