import SymmetricSubgroupAsymptotics.TernaryNormalizerOrbitPrefix
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Original ternary Sylow subgroups and their eight orbits

A binary quotient preserves the single factor of three in the original
group order inside its kernel. Its actual ternary Sylow subgroup therefore
has order three. Semiregularity on twenty-four original points gives eight
actual orbits and supplies the normalizer-prefix theorem.

The final importer obtains semiregularity from an equivariant top action
with binary kernel. The finite top inputs are only its single factor of
three and fixed-point-freeness of its nonidentity elements of exponent
three. No original normal subgroup is enumerated.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.TernaryKernelSylowSemiregular

open TernaryNormalizerOrbitPrefix
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem card_kernel_mul_card_target
    {G Q : Type} [Group G] [Group Q]
    (pi : G →* Q) (hpi : Function.Surjective pi) :
    Nat.card pi.ker * Nat.card Q = Nat.card G := by
  have hi : pi.ker.index = Nat.card Q := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hpi, Subgroup.card_top]
  rw [← hi]
  exact pi.ker.card_mul_index

theorem kernelSylow_card_three
    {G Q : Type} [Group G] [Finite G] [Group Q] [Finite Q]
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : IsPGroup 2 Q)
    (hthree : 3 ∣ Nat.card G) (hnine : ¬ 9 ∣ Nat.card G)
    (P : Sylow 3 pi.ker) : Nat.card (P.map pi.ker.subtype) = 3 := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hnot : ¬ 3 ∣ Nat.card Q := by
    rw [hk]
    intro h
    exact (by decide : ¬ 3 ∣ 2) ((by decide : Nat.Prime 3).dvd_of_dvd_pow h)
  have hker : 3 ∣ Nat.card pi.ker := by
    rw [← card_kernel_mul_card_target pi hpi] at hthree
    exact ((by decide : Nat.Prime 3).dvd_mul.mp hthree).resolve_right hnot
  have hPthree : 3 ∣ Nat.card P := P.dvd_card_of_dvd_card hker
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hnlt : n < 2 := by
    by_contra h
    have hdiv : 9 ∣ Nat.card P := by
      rw [hn]
      exact pow_dvd_pow 3 (by omega : 2 ≤ n)
    exact hnine (hdiv.trans
      ((P : Subgroup pi.ker).card_subgroup_dvd_card.trans pi.ker.card_subgroup_dvd_card))
  have hnzero : n ≠ 0 := by
    intro h
    rw [hn, h] at hPthree
    norm_num at hPthree
  have hPcard : Nat.card P = 3 := by
    rw [hn, show n = 1 by omega, pow_one]
  let e := (P : Subgroup pi.ker).equivMapOfInjective pi.ker.subtype
    Subtype.val_injective
  exact (Nat.card_congr e.toEquiv).symm.trans hPcard

/-- Counting actual free orbits uses an explicit orbit bijection. -/
theorem orbit_card_of_semiregular
    {G X : Type} [Group G] [MulAction G X] (H : Subgroup G)
    (hfree : ∀ (a : H) (x : X), (a : G) • x = x → a = 1) (x : X) :
    Nat.card (MulAction.orbit H x) = Nat.card H := by
  let f : H → MulAction.orbit H x := fun a ↦ ⟨a • x, MulAction.mem_orbit x a⟩
  have hf : Function.Injective f := by
    intro a b h
    have he : (a : G) • x = (b : G) • x := congrArg Subtype.val h
    have hone : b⁻¹ * a = 1 := hfree (b⁻¹ * a) x (by
      change ((b : G)⁻¹ * (a : G)) • x = x
      rw [mul_smul, he, inv_smul_smul])
    exact (inv_mul_eq_one.mp hone).symm
  have hs : Function.Surjective f := by
    rintro ⟨y, a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf, hs⟩)).symm

theorem eight_orbits_of_semiregular_twentyFour
    {G X : Type} [Group G] [MulAction G X] [Finite X]
    (H : Subgroup G) (hH : Nat.card H = 3) (hX : Nat.card X = 24)
    (hfree : ∀ (a : H) (x : X), (a : G) • x = x → a = 1) :
    Nat.card (Orbits (X := X) H) = 8 := by
  classical
  letI : Fintype (Orbits (X := X) H) := Fintype.ofFinite _
  have hsum : (∑ o : Orbits (X := X) H, Nat.card (MulAction.orbit H o.out)) =
      Nat.card X := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (MulAction.selfEquivSigmaOrbits H X).symm
  simp only [orbit_card_of_semiregular H hfree, hH, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, hX] at hsum
  omega

/-- Every original binary quotient is handled by the same geometric
condition on the original action. -/
theorem binaryPrefixOrbitInput_of_semiregular_twentyFour
    {G X Q : Type} [Group G] [Finite G] [MulAction G X]
    [Finite X] [FaithfulSMul G X] [Group Q] [Finite Q]
    (hX : Nat.card X = 24) (hthree : 3 ∣ Nat.card G) (hnine : ¬ 9 ∣ Nat.card G)
    (hfree : ∀ (g : G), g ^ 3 = 1 → g ≠ 1 → ∀ x : X, g • x ≠ x)
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : IsPGroup 2 Q) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput Q
      (degreeTwoPairRelativeProfile 1 0 0 4)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 3 pi.ker := Classical.choice inferInstance
  have hP := kernelSylow_card_three pi hpi hQ hthree hnine P
  apply binaryPrefixOrbitInput_of_kernelSylow (X := X) pi hpi hQ P hP
  apply eight_orbits_of_semiregular_twentyFour (P.map pi.ker.subtype) hP hX
  intro a x hax
  by_contra ha
  have ha3 : (a : G) ^ 3 = 1 := by
    have h : a ^ 3 = 1 := by simpa only [hP] using (pow_card_eq_one' (x := a))
    exact congrArg Subtype.val h
  exact hfree (a : G) ha3 (fun h ↦ ha (Subtype.ext h)) x hax

/-- A nonidentity ternary element cannot disappear in a binary kernel.
Its fixed point would give a fixed point in the actual top action. -/
theorem semiregular_of_binary_kernel_top
    {G T X Y : Type} [Group G] [Group T] [MulAction G X] [MulAction T Y]
    (tau : G →* T) (hker : IsPGroup 2 tau.ker)
    (pointMap : X → Y)
    (hequiv : ∀ (g : G) (x : X), pointMap (g • x) = tau g • pointMap x)
    (hfree : ∀ (t : T), t ^ 3 = 1 → t ≠ 1 → ∀ y : Y, t • y ≠ y) :
    ∀ (g : G), g ^ 3 = 1 → g ≠ 1 → ∀ x : X, g • x ≠ x := by
  intro g hg hgne x hgx
  have ht : tau g ≠ 1 := by
    intro h
    let a : tau.ker := ⟨g, h⟩
    have ha : a ^ 3 = 1 := Subtype.ext hg
    have haone : a = 1 := by
      apply (hker.powEquiv (by decide : Nat.Coprime 2 3)).injective
      simpa only [IsPGroup.powEquiv_apply, one_pow] using ha
    exact hgne (congrArg Subtype.val haone)
  apply hfree (tau g) (by rw [← map_pow, hg, map_one]) ht (pointMap x)
  rw [← hequiv, hgx]

/-- A reusable exceptional-core binary branch. Its finite inputs concern
only the literal top order and literal cubic fixed points. -/
theorem binaryPrefixOrbitInput_of_binary_kernel_top
    {G T X Y Q : Type} [Group G] [Finite G] [Group T] [Finite T]
    [MulAction G X] [Finite X] [FaithfulSMul G X] [MulAction T Y]
    [Group Q] [Finite Q]
    (hX : Nat.card X = 24)
    (tau : G →* T) (htau : Function.Surjective tau) (hker : IsPGroup 2 tau.ker)
    (hthree : 3 ∣ Nat.card T) (hnine : ¬ 9 ∣ Nat.card T)
    (pointMap : X → Y)
    (hequiv : ∀ (g : G) (x : X), pointMap (g • x) = tau g • pointMap x)
    (hfree : ∀ (t : T), t ^ 3 = 1 → t ≠ 1 → ∀ y : Y, t • y ≠ y)
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : IsPGroup 2 Q) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput Q
      (degreeTwoPairRelativeProfile 1 0 0 4)) := by
  have hthreeG : 3 ∣ Nat.card G :=
    hthree.trans (Subgroup.card_dvd_of_surjective tau htau)
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hnineG : ¬ 9 ∣ Nat.card G := by
    intro h
    rw [← card_kernel_mul_card_target tau htau, hk] at h
    have hc : Nat.Coprime 9 (2 ^ k) := (by decide : Nat.Coprime 9 2).pow_right k
    exact hnine (hc.dvd_of_dvd_mul_left h)
  exact binaryPrefixOrbitInput_of_semiregular_twentyFour hX hthreeG hnineG
    (semiregular_of_binary_kernel_top tau hker pointMap hequiv hfree) pi hpi hQ

end SymmetricSubgroupAsymptotics.TernaryKernelSylowSemiregular
