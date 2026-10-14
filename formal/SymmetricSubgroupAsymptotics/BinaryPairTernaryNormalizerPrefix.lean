import SymmetricSubgroupAsymptotics.TernaryKernelSylowSemiregular
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairTopStructuralAnchor

/-!
# The ternary normalizer branch on original twelve-pair realizations

The original pair frame supplies the equivariant point projection and its
binary kernel. A literal top certificate needs only an order divisible by
three but not nine and a fixed-point check for its nonidentity cubic
elements. It then handles every actual original binary quotient.

The realization's existing module-action binding is proved to bind the
underlying point permutations as well, so the certificate is checked on
the literal top, not on an independently chosen abstract action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryPairTernaryNormalizerPrefix

open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

theorem frame_binary_quotient_orbitInput
    {X I : Type} [Finite X] [Finite I] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (hI : Nat.card I = 12)
    (hthree : 3 ∣ Nat.card F.top.range) (hnine : ¬ 9 ∣ Nat.card F.top.range)
    (hfree : ∀ t : F.top.range, t ^ 3 = 1 → t ≠ 1 → ∀ i : I, t • i ≠ i)
    (N : Subgroup U) [N.Normal] (hQ : IsPGroup 2 (U ⧸ N)) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput (U ⧸ N)
      (degreeTwoPairRelativeProfile 1 0 0 4)) := by
  have hX : Nat.card X = 24 := by
    rw [← Nat.card_congr F.frame, Nat.card_prod, hI, Nat.card_zmod]
  have hker : IsPGroup 2 F.top.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact F.kernel_isPGroup
  apply TernaryKernelSylowSemiregular.binaryPrefixOrbitInput_of_binary_kernel_top
    hX F.top.rangeRestrict F.top.rangeRestrict_surjective hker hthree hnine
    (fun x ↦ (F.frame.symm x).1) ?_ hfree
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hQ
  intro u x
  obtain ⟨p, rfl⟩ := F.frame.surjective x
  change (F.frame.symm ((u : Equiv.Perm X) (F.frame p))).1 =
    F.top u (F.frame.symm (F.frame p)).1
  rw [F.intertwine, F.frame.symm_apply_apply]

/-- The full function-module binding determines the original point
permutation, since binary-valued functions separate distinct points. -/
theorem realization_topEquiv_perm_eq
    {s : ℕ} {D : DegreeTwoPairTopFiniteInterface s} {p : PreE7PairActionClass s}
    (R : DegreeTwoPairTopRealization D p) (g : D.top) :
    ((R.topEquiv g : R.frame.top.range) : Equiv.Perm (Fin s)) =
      (g : Equiv.Perm (Fin s)) := by
  classical
  apply inv_injective
  apply Equiv.ext
  intro i
  by_contra hne
  let v : Fin s → ZMod 2 := fun j ↦
    if j = (g : Equiv.Perm (Fin s))⁻¹ i then 1 else 0
  have h := congrFun (R.module_action_eq g v) i
  change v ((g : Equiv.Perm (Fin s))⁻¹ i) =
    v (((R.topEquiv g : R.frame.top.range) : Equiv.Perm (Fin s))⁻¹ i) at h
  exact one_ne_zero (by simpa only [v, if_pos rfl, if_neg hne] using h)

/-- These are finite order and original point-action checks. There is no
rank bound, quotient coverage, or character feasibility field. -/
structure LiteralTopCertificate (D : DegreeTwoPairTopFiniteInterface 12) : Prop where
  three_dvd : 3 ∣ Nat.card D.top
  nine_not_dvd : ¬ 9 ∣ Nat.card D.top
  cubic_fixedPointFree :
    ∀ t : D.top, t ^ 3 = 1 → t ≠ 1 → ∀ i : Fin 12, t • i ≠ i

theorem literal_binary_quotient_orbitInput
    {D : DegreeTwoPairTopFiniteInterface 12} (C : LiteralTopCertificate D)
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hQ : IsPGroup 2 (preE7PairAction 12 p ⧸ N.1)) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput
      (preE7PairAction 12 p ⧸ N.1) (degreeTwoPairRelativeProfile 1 0 0 4)) := by
  letI : N.1.Normal := N.2
  have hthree : 3 ∣ Nat.card R.frame.top.range := by
    rw [← Nat.card_congr R.topEquiv.toEquiv]
    exact C.three_dvd
  have hnine : ¬ 9 ∣ Nat.card R.frame.top.range := by
    rw [← Nat.card_congr R.topEquiv.toEquiv]
    exact C.nine_not_dvd
  apply frame_binary_quotient_orbitInput R.frame (by simp) hthree hnine ?_ N.1 hQ
  intro t ht htne i hti
  let g := R.topEquiv.symm t
  have hg : g ^ 3 = 1 := by
    apply R.topEquiv.injective
    simpa only [g, map_pow, map_one, MulEquiv.apply_symm_apply] using ht
  have hgne : g ≠ 1 := by
    intro h
    apply htne
    simpa only [g, MulEquiv.apply_symm_apply, map_one] using congrArg R.topEquiv h
  have he : (t : Equiv.Perm (Fin 12)) = (g : Equiv.Perm (Fin 12)) := by
    simpa only [g, MulEquiv.apply_symm_apply] using realization_topEquiv_perm_eq R g
  apply C.cubic_fixedPointFree g hg hgne i
  change (g : Equiv.Perm (Fin 12)) i = i
  rw [← he]
  exact hti

/-- Binaryity of the literal top quotient implies binaryity of the same
original quotient through its checked elementary pair-section kernel. -/
theorem literal_binary_top_quotient_orbitInput
    {D : DegreeTwoPairTopFiniteInterface 12} (C : LiteralTopCertificate D)
    {p : PreE7PairActionClass 12} (R : DegreeTwoPairTopRealization D p)
    (N : {N : Subgroup (preE7PairAction 12 p) // N.Normal})
    (hbinaryTop : IsPGroup 2 (D.top ⧸ D.normalRegistry.state (R.topNormalState N))) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput
      (preE7PairAction 12 p ⧸ N.1) (degreeTwoPairRelativeProfile 1 0 0 4)) := by
  letI : N.1.Normal := N.2
  exact literal_binary_quotient_orbitInput C R N
    (isPGroup_of_kernel_and_target (R.quotientMap N)
      (R.quotientMap_kernel_isPGroup N) hbinaryTop)

end SymmetricSubgroupAsymptotics.BinaryPairTernaryNormalizerPrefix
