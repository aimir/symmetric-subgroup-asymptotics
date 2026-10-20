import SymmetricSubgroupAsymptotics.BinaryNormalizerImagePrefix
import SymmetricSubgroupAsymptotics.Non2SylowReduction
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# A ternary normalizer acting on its actual original orbits

The normalizer acts both by conjugation on the actual ternary subgroup
and by permutation on its actual point orbits. The common kernel has
exponent three: an element in it commutes with the ternary subgroup and
moves each point within its original orbit. It therefore dies in every
binary quotient.

This proves that the joint action image, with every correlation retained,
maps onto the same original binary quotient. When the ternary subgroup
has order three and eight point orbits, the image supplies the designated
binary prefix. The final theorem uses the actual Sylow subgroup of the
original quotient kernel, so Frattini supplies surjectivity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped IsMulCommutative

namespace SymmetricSubgroupAsymptotics.TernaryNormalizerOrbitPrefix

variable {G X : Type} [Group G] [MulAction G X] (H : Subgroup G)

abbrev Orbits := MulAction.orbitRel.Quotient H X

def orbitMap (g : Subgroup.normalizer (H : Set G)) :
    Orbits (X := X) H → Orbits (X := X) H :=
  Quotient.map (fun x ↦ (g : G) • x) (by
    rintro x y ⟨a, ha⟩
    refine ⟨⟨(g : G) * (a : G) * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp g.property (a : G)).mp a.property⟩, ?_⟩
    change (a : G) • y = x at ha
    change ((g : G) * (a : G) * (g : G)⁻¹) • ((g : G) • y) = (g : G) • x
    simp only [mul_smul, inv_smul_smul, ha])

theorem orbitMap_one (o : Orbits (X := X) H) : orbitMap H 1 o = o := by
  refine Quotient.inductionOn o ?_
  intro x
  change Quotient.mk _ ((1 : G) • x) = Quotient.mk _ x
  rw [one_smul]

theorem orbitMap_mul (g h : Subgroup.normalizer (H : Set G)) (o : Orbits (X := X) H) :
    orbitMap H (g * h) o = orbitMap H g (orbitMap H h o) := by
  refine Quotient.inductionOn o ?_
  intro x
  change Quotient.mk _ (((g : G) * (h : G)) • x) =
    Quotient.mk _ ((g : G) • ((h : G) • x))
  rw [mul_smul]

def orbitPermHom : Subgroup.normalizer (H : Set G) →* Equiv.Perm (Orbits (X := X) H) where
  toFun g := {
    toFun := orbitMap H g
    invFun := orbitMap H g⁻¹
    left_inv := by intro o; rw [← orbitMap_mul, inv_mul_cancel, orbitMap_one]
    right_inv := by intro o; rw [← orbitMap_mul, mul_inv_cancel, orbitMap_one] }
  map_one' := by ext o; exact orbitMap_one H o
  map_mul' g h := by ext o; exact orbitMap_mul H g h o

def jointAction : Subgroup.normalizer (H : Set G) →*
    MulAut H × Equiv.Perm (Orbits (X := X) H) :=
  H.normalizerMonoidHom.prod (orbitPermHom H)

/-- The kernel argument uses each original orbit, not an independent
choice of a permutation or a quotient action on the original points. -/
theorem jointAction_kernel_cube [FaithfulSMul G X]
    (hH : ∀ a : H, a ^ 3 = 1)
    (g : Subgroup.normalizer (H : Set G)) (hg : g ∈ (jointAction (X := X) H).ker) :
    g ^ 3 = 1 := by
  have hconj : H.normalizerMonoidHom g = 1 := congrArg Prod.fst hg
  have horbit : orbitPermHom (X := X) H g = 1 := congrArg Prod.snd hg
  have hcomm (a : H) : (g : G) * (a : G) = (a : G) * (g : G) := by
    have h := congrArg (fun f : MulAut H ↦ (f a : G)) hconj
    change (g : G) * (a : G) * (g : G)⁻¹ = (a : G) at h
    exact mul_inv_eq_iff_eq_mul.mp h
  apply Subtype.ext
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  have ho := congrArg (fun f : Equiv.Perm (Orbits (X := X) H) ↦
    f (Quotient.mk _ x)) horbit
  change (Quotient.mk _ ((g : G) • x) : Orbits (X := X) H) = Quotient.mk _ x at ho
  obtain ⟨a, ha⟩ := Quotient.exact ho
  change (a : G) • x = (g : G) • x at ha
  have hc (y : X) : (g : G) • ((a : G) • y) = (a : G) • ((g : G) • y) := by
    rw [← mul_smul, ← mul_smul, hcomm a]
  have ha3 : (a : G) ^ 3 = 1 := congrArg Subtype.val (hH a)
  change (g : G) ^ 3 • x = (1 : G) • x
  calc
    (g : G) ^ 3 • x = (g : G) • ((g : G) • ((g : G) • x)) := by
      simp only [pow_succ, pow_zero, one_mul, mul_smul]
    _ = (g : G) • ((g : G) • ((a : G) • x)) := by rw [ha]
    _ = (g : G) • ((a : G) • ((g : G) • x)) := by rw [hc]
    _ = (a : G) • ((g : G) • ((g : G) • x)) := hc _
    _ = (a : G) • ((g : G) • ((a : G) • x)) := by rw [ha]
    _ = (a : G) • ((a : G) • ((g : G) • x)) := by rw [hc]
    _ = (a : G) • ((a : G) • ((a : G) • x)) := by rw [ha]
    _ = (a : G) ^ 3 • x := by simp only [pow_succ, pow_zero, one_mul, mul_smul]
    _ = (1 : G) • x := by rw [ha3]

theorem jointAction_kernel_le_binary_kernel
    [FaithfulSMul G X] {Q : Type} [Group Q]
    (hH : ∀ a : H, a ^ 3 = 1)
    (pi : G →* Q) (hQ : IsPGroup 2 Q) :
    (jointAction (X := X) H).ker ≤
      (pi.comp (Subgroup.normalizer (H : Set G)).subtype).ker := by
  intro g hg
  have hg3 : (g : G) ^ 3 = 1 :=
    congrArg Subtype.val (jointAction_kernel_cube H hH g hg)
  change pi (g : G) = 1
  apply (hQ.powEquiv (by decide : Nat.Coprime 2 3)).injective
  change pi (g : G) ^ 3 = 1 ^ 3
  rw [← map_pow, hg3, map_one, one_pow]

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- An actual ternary normalizer supplement with eight original orbits
supplies the exceptional binary branch on its original target. -/
theorem binaryPrefixOrbitInput_of_normalizer
    [Finite G] [Finite X] [FaithfulSMul G X]
    {Q : Type} [Group Q] [Finite Q]
    (hHcard : Nat.card H = 3) (horbits : Nat.card (Orbits (X := X) H) = 8)
    (pi : G →* Q)
    (hpi : Function.Surjective (pi.comp (Subgroup.normalizer (H : Set G)).subtype))
    (hQ : IsPGroup 2 Q) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput Q
      (degreeTwoPairRelativeProfile 1 0 0 4)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : IsCyclic H := isCyclic_of_prime_card hHcard
  have hH : ∀ a : H, a ^ 3 = 1 := fun a ↦ by
    simpa only [hHcard] using (pow_card_eq_one' (x := a))
  have hAut : Nat.card (MulAut H) = 2 := by
    rw [IsCyclic.card_mulAut, hHcard]
    decide
  letI : IsCyclic (MulAut H) := isCyclic_of_prime_card hAut
  letI : IsMulCommutative (MulAut H) := IsCyclic.isMulCommutative
  let phi := jointAction (X := X) H
  let rho := pi.comp (Subgroup.normalizer (H : Set G)).subtype
  have hker : phi.rangeRestrict.ker ≤ rho.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact jointAction_kernel_le_binary_kernel H hH pi hQ
  let q : phi.range →* Q :=
    phi.rangeRestrict.liftOfSurjective phi.rangeRestrict_surjective ⟨rho, hker⟩
  have hq_apply (g : Subgroup.normalizer (H : Set G)) :
      q (phi.rangeRestrict g) = rho g :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨g, hg⟩ := hpi y
    exact ⟨phi.rangeRestrict g, (hq_apply g).trans hg⟩
  let alpha : phi.range →* MulAut H :=
    (MonoidHom.fst _ _).comp phi.range.subtype
  let beta : phi.range →* Equiv.Perm (Orbits (X := X) H) :=
    (MonoidHom.snd _ _).comp phi.range.subtype
  have hfaithful : Function.Injective (alpha.prod beta) := by
    intro x y h
    exact Subtype.ext h
  exact BinaryNormalizerImagePrefix.binaryPrefixOrbitInput_of_eight_orbit_image
    alpha beta hfaithful hAut.le horbits q hq hQ

omit H in
/-- Frattini provides the supplement from the actual Sylow subgroup of
the original kernel. The two geometric inputs concern that subgroup and
its original point orbits; no normal-registry completeness is used. -/
theorem binaryPrefixOrbitInput_of_kernelSylow
    [Finite G] [Finite X] [FaithfulSMul G X]
    {Q : Type} [Group Q] [Finite Q]
    (pi : G →* Q) (hpi : Function.Surjective pi) (hQ : IsPGroup 2 Q)
    (P : Sylow 3 pi.ker)
    (hPcard : Nat.card (P.map pi.ker.subtype) = 3)
    (horbits : Nat.card (Orbits (X := X) (P.map pi.ker.subtype)) = 8) :
    Nonempty (DegreeTwoPairRelativeKernelOrbitInput Q
      (degreeTwoPairRelativeProfile 1 0 0 4)) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact binaryPrefixOrbitInput_of_normalizer (P.map pi.ker.subtype)
    hPcard horbits pi (quotientSylowNormalizer_surjective pi hpi P) hQ

end SymmetricSubgroupAsymptotics.TernaryNormalizerOrbitPrefix
