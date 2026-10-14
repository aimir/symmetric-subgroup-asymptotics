import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveExceptionalOriginalQuotients
import SymmetricSubgroupAsymptotics.BinaryPairTernaryNormalizerPrefix
import SymmetricSubgroupAsymptotics.TernarySemiregularS3QuotientAnchor

/-!
# Literal S₃ geometry for exceptional twelve-pair tops

An actual onto map to S₃ with binary kernel and an equivariant projection
of the literal twelve points onto three labels imply the entire original
quotient argument. The cardinal's odd part and cubic semiregularity are
derived, rather than requested as separate finite certificates.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace DegreeTwoTwelveSymmetricThreeGeometry

open BinaryPairTernaryNormalizerPrefix
open DegreeTwoTwelveExceptionalOriginalQuotients

structure TopGeometry (D : DegreeTwoPairTopFiniteInterface 12) : Type where
  beta : D.top →* Equiv.Perm (Fin 3)
  onto : Function.Surjective beta
  kernel_binary : IsPGroup 2 beta.ker
  project : Fin 12 → Fin 3
  equivariant : ∀ (g : D.top) (x : Fin 12), project (g • x) = beta g • project x

private theorem symmetricThree_cubic_free
    (g : Equiv.Perm (Fin 3)) (hg : g ^ 3 = 1) (hne : g ≠ 1) (i : Fin 3) :
    g • i ≠ i := by
  decide +kernel +revert

/-- Binary-by-S₃ already forces exactly one ternary factor in the order. -/
theorem card_of_binary_kernel_symmetricThree
    {G : Type} [Group G] [Finite G]
    (beta : G →* Equiv.Perm (Fin 3)) (hbeta : Function.Surjective beta)
    (hker : IsPGroup 2 beta.ker) : ∃ a : ℕ, Nat.card G = 2 ^ a * 3 := by
  obtain ⟨a, ha⟩ := hker.exists_card_eq
  have hS : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have hi : beta.ker.index = 6 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hbeta, Subgroup.card_top, hS]
  refine ⟨a + 1, ?_⟩
  calc
    Nat.card G = Nat.card beta.ker * beta.ker.index := beta.ker.card_mul_index.symm
    _ = 2 ^ (a + 1) * 3 := by rw [ha, hi, pow_add]; ring

namespace TopGeometry

variable {D : DegreeTwoPairTopFiniteInterface 12} (C : TopGeometry D)

include C in
theorem cubic_fixedPointFree :
    ∀ g : D.top, g ^ 3 = 1 → g ≠ 1 → ∀ x : Fin 12, g • x ≠ x :=
  TernaryKernelSylowSemiregular.semiregular_of_binary_kernel_top
    C.beta C.kernel_binary C.project C.equivariant symmetricThree_cubic_free

def literalTopCertificate : LiteralTopCertificate D := by
  obtain ⟨a, ha⟩ := card_of_binary_kernel_symmetricThree C.beta C.onto C.kernel_binary
  refine ⟨?_, ?_, C.cubic_fixedPointFree⟩
  · rw [ha]
    exact dvd_mul_left 3 (2 ^ a)
  · rw [ha]
    intro h
    have hc : Nat.Coprime 9 (2 ^ a) := (by decide : Nat.Coprime 9 2).pow_right a
    exact (by decide : ¬ 9 ∣ 3) (hc.dvd_of_dvd_mul_left h)

variable {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p)

def originalTopMap : preE7PairAction 12 p →* D.top :=
  R.topEquiv.symm.toMonoidHom.comp R.frame.top.rangeRestrict

theorem originalTopMap_onto : Function.Surjective (originalTopMap R) :=
  R.topEquiv.symm.surjective.comp R.frame.top.rangeRestrict_surjective

theorem originalTopMap_kernel_binary : IsPGroup 2 (originalTopMap R).ker := by
  have heq : (originalTopMap R).ker = R.frame.top.ker := by
    ext g
    change R.topEquiv.symm (R.frame.top.rangeRestrict g) = 1 ↔ R.frame.top g = 1
    rw [R.topEquiv.symm.map_eq_one_iff]
    constructor
    · exact fun h ↦ congrArg Subtype.val h
    · exact fun h ↦ Subtype.ext h
  rw [heq]
  exact R.frame.kernel_isPGroup

theorem originalTopMap_perm (g : preE7PairAction 12 p) :
    ((originalTopMap R g : D.top) : Equiv.Perm (Fin 12)) = R.frame.top g := by
  calc
    ((originalTopMap R g : D.top) : Equiv.Perm (Fin 12)) =
        ((R.topEquiv (originalTopMap R g) : R.frame.top.range) : Equiv.Perm (Fin 12)) :=
      (realization_topEquiv_perm_eq R (originalTopMap R g)).symm
    _ = R.frame.top g := by
      change ((R.topEquiv (R.topEquiv.symm (R.frame.top.rangeRestrict g)) :
        R.frame.top.range) : Equiv.Perm (Fin 12)) = R.frame.top g
      exact congrArg (fun t : R.frame.top.range ↦ (t : Equiv.Perm (Fin 12)))
        (R.topEquiv.apply_symm_apply (R.frame.top.rangeRestrict g))

def originalBeta : preE7PairAction 12 p →* Equiv.Perm (Fin 3) :=
  C.beta.comp (originalTopMap R)

theorem originalBeta_onto : Function.Surjective (C.originalBeta R) :=
  C.onto.comp (originalTopMap_onto R)

theorem originalBeta_kernel_binary : IsPGroup 2 (C.originalBeta R).ker :=
  C.kernel_binary.comap_of_ker_isPGroup (originalTopMap R)
    (originalTopMap_kernel_binary R)

include C R in
theorem original_card : ∃ a : ℕ, Nat.card (preE7PairAction 12 p) = 2 ^ a * 3 :=
  card_of_binary_kernel_symmetricThree (C.originalBeta R) (C.originalBeta_onto R)
    (C.originalBeta_kernel_binary R)

include C R in
theorem original_cubic_fixedPointFree :
    ∀ g : preE7PairAction 12 p, g ^ 3 = 1 → g ≠ 1 → ∀ x : Fin 24, g • x ≠ x := by
  apply TernaryKernelSylowSemiregular.semiregular_of_binary_kernel_top
    (originalTopMap R) (originalTopMap_kernel_binary R)
    (fun x ↦ (R.frame.frame.symm x).1) ?_ C.cubic_fixedPointFree
  intro g x
  obtain ⟨v, rfl⟩ := R.frame.frame.surjective x
  change (R.frame.frame.symm ((g : Equiv.Perm (Fin 24)) (R.frame.frame v))).1 =
    ((originalTopMap R g : D.top) : Equiv.Perm (Fin 12))
      (R.frame.frame.symm (R.frame.frame v)).1
  rw [originalTopMap_perm, R.frame.intertwine, R.frame.frame.symm_apply_apply]

def nonbinaryAnchor (hZmud : ZmudFaithfulCharacterTupleInput)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hQ : ¬ IsPGroup 2 (preE7PairAction 12 p ⧸ N.1)) :
    DegreeTwoPairRelativeKernelAnchor (preE7PairAction 12 p ⧸ N.1)
      (degreeTwoPairOrdinaryRelativeProfile 1 3) := by
  letI : N.1.Normal := N.2
  let orderData := C.original_card R
  exact ternarySemiregular_s3_nonbinary_normal_quotient_anchor hZmud
    (X := Fin 24) (by simp) orderData.choose_spec (C.original_cubic_fixedPointFree R)
    (C.originalBeta R) (C.originalBeta_onto R) (C.originalBeta_kernel_binary R) N.1 hQ

/-- The finite literal geometry resolves every original quotient. -/
def certificate : RowCertificate D :=
  RowCertificate.ofSymmetricThreeCore
    (fun _hZmud {_p} R N hbinaryTop ↦
      (Classical.choice (literal_binary_top_quotient_orbitInput
        C.literalTopCertificate R N hbinaryTop)).anchor)
    (fun hZmud {_p} R N hnonbinaryTop ↦ by
      letI : N.1.Normal := N.2
      apply C.nonbinaryAnchor R hZmud N
      intro hQ
      exact hnonbinaryTop
        (hQ.of_surjective (R.quotientMap N) (R.quotientMap_surjective N)))

end TopGeometry
end DegreeTwoTwelveSymmetricThreeGeometry
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
