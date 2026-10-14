import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of actual ternary Sylow subgroups lift through binary kernels

Let `pi : G →* Q` be surjective with binary kernel, and let `P` be an
actual Sylow three subgroup of `G`. The original map sends `C_G(P)` onto
`C_Q(pi(P))`.

The first step is a general normalizer-image lemma. Sylow conjugacy inside
`pi⁻¹(pi(P))` corrects a lift to normalize `P`; an additional element of
`P` removes the change in its image. Coprimality makes `pi` injective on
`P`, so a normalizer lift of an element centralizing `pi(P)` centralizes
`P` itself. All subgroup maps and centralizers are literal. No splitting
or cohomological input is assumed, and `P` need not have order three.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace CoprimeTernaryCentralizerLift

/-- A lift whose image normalizes the image of a Sylow subgroup can be
corrected, without changing its image, to normalize that actual Sylow
subgroup. This step does not require a coprime kernel. -/
theorem sylowNormalizer_exists_lift
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    {p : ℕ} [Fact p.Prime] (pi : G →* Q) (P : Sylow p G)
    (g : G) (hg : pi g ∈ Subgroup.normalizer (P.map pi : Set Q)) :
    ∃ n ∈ Subgroup.normalizer (P : Set G), pi n = pi g := by
  let H : Subgroup G := (P.map pi).comap pi
  have hP : (P : Subgroup G) ≤ H := by
    intro x hx
    exact ⟨x, hx, rfl⟩
  have hgH : g ∈ Subgroup.normalizer (H : Set G) :=
    (Subgroup.le_normalizer_comap (H := P.map pi) pi) hg
  have hgP : ((g • P : Sylow p G) : Subgroup G) ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hgH x).mp (hP hx)
  obtain ⟨t, ht⟩ := MulAction.exists_smul_eq H
    ((g • P).subtype hgP) (P.subtype hP)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at ht
  have htg : (t : G) * g ∈ Subgroup.normalizer (P : Set G) :=
    Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective ht)
  have htimage : pi (t : G) ∈ P.map pi := t.property
  obtain ⟨x, hx, hxt⟩ := htimage
  refine ⟨x⁻¹ * ((t : G) * g), ?_, ?_⟩
  · exact (Subgroup.normalizer (P : Set G)).mul_mem
      ((Subgroup.normalizer (P : Set G)).inv_mem
        ((P : Subgroup G).le_normalizer hx)) htg
  · rw [map_mul, map_inv, map_mul, hxt, inv_mul_cancel_left]

/-- Under a surjection, the image of the actual Sylow normalizer is the
normalizer of the actual image subgroup. -/
theorem sylow_map_normalizer_eq
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    {p : ℕ} [Fact p.Prime] (pi : G →* Q)
    (hpi : Function.Surjective pi) (P : Sylow p G) :
    (Subgroup.normalizer (P : Set G)).map pi =
      Subgroup.normalizer (P.map pi : Set Q) := by
  apply le_antisymm
  · exact Subgroup.le_normalizer_map (H := (P : Subgroup G)) pi
  · intro q hq
    obtain ⟨g, rfl⟩ := hpi q
    obtain ⟨n, hn, hng⟩ := sylowNormalizer_exists_lift pi P g hq
    exact ⟨n, hn, hng⟩

/-- The original homomorphism is injective on every ternary subgroup
when its literal kernel is binary. -/
theorem ternary_restriction_injective
    {G Q : Type*} [Group G] [Group Q]
    (pi : G →* Q) (hker : IsPGroup 2 pi.ker)
    (P : Subgroup G) (hP : IsPGroup 3 P) :
    Function.Injective (pi.comp P.subtype) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdis : Disjoint P pi.ker :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) P pi.ker hP hker
  intro x y hxy
  apply Subtype.ext
  have hmem : (x : G) * (y : G)⁻¹ ∈ pi.ker := by
    change pi ((x : G) * (y : G)⁻¹) = 1
    change pi (x : G) = pi (y : G) at hxy
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hone : (x : G) * (y : G)⁻¹ = 1 :=
    Subgroup.disjoint_def.mp hdis (P.mul_mem x.property (P.inv_mem y.property)) hmem
  exact mul_inv_eq_one.mp hone

/-- Injectivity on the ternary subgroup upgrades an actual normalizer
lift of a centralizing image element to an actual centralizer element. -/
theorem mem_centralizer_of_normalizer_and_image
    {G Q : Type*} [Group G] [Group Q]
    (pi : G →* Q) (hker : IsPGroup 2 pi.ker)
    (P : Subgroup G) (hP : IsPGroup 3 P)
    (g : G) (hg : g ∈ Subgroup.normalizer (P : Set G))
    (himage : pi g ∈ Subgroup.centralizer (P.map pi : Set Q)) :
    g ∈ Subgroup.centralizer (P : Set G) := by
  intro x hx
  have hxconj : g * x * g⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have he : pi (g * x * g⁻¹) = pi x := by
    have hc : pi x * pi g = pi g * pi x := himage (pi x) ⟨x, hx, rfl⟩
    rw [map_mul, map_mul, map_inv, ← hc, mul_inv_cancel_right]
  have hsub : (⟨g * x * g⁻¹, hxconj⟩ : P) = ⟨x, hx⟩ :=
    ternary_restriction_injective pi hker P hP he
  have hconj : g * x * g⁻¹ = x := congrArg Subtype.val hsub
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

/-- Centralizers of the original Sylow three subgroup map onto the
centralizer of its image through a surjection with binary kernel. -/
theorem map_centralizer_eq
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker) (P : Sylow 3 G) :
    (Subgroup.centralizer (P : Set G)).map pi =
      Subgroup.centralizer (P.map pi : Set Q) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩ q ⟨x, hx, rfl⟩
    simpa only [map_mul] using congrArg pi (hg x hx)
  · intro q hq
    have hqn : q ∈ (Subgroup.normalizer (P : Set G)).map pi := by
      rw [sylow_map_normalizer_eq pi hpi P]
      exact Subgroup.centralizer_le_normalizer _ hq
    obtain ⟨g, hg, hgq⟩ := hqn
    have hcentral : g ∈ Subgroup.centralizer (P : Set G) :=
      mem_centralizer_of_normalizer_and_image pi hker P P.isPGroup' g hg
        (by rw [hgq]; exact hq)
    exact ⟨g, hcentral, hgq⟩

/-- Restriction of the original map to the literal source and target
centralizers. This map is defined without any surjectivity assumption. -/
def centralizerMap
    {G Q : Type*} [Group G] [Group Q]
    (pi : G →* Q) (P : Subgroup G) :
    Subgroup.centralizer (P : Set G) →*
      Subgroup.centralizer (P.map pi : Set Q) :=
  (pi.comp (Subgroup.centralizer (P : Set G)).subtype).codRestrict
    (Subgroup.centralizer (P.map pi : Set Q)) (by
      intro g q hq
      obtain ⟨x, hx, rfl⟩ := hq
      simpa only [map_mul] using congrArg pi (g.property x hx))

@[simp] theorem centralizerMap_apply
    {G Q : Type*} [Group G] [Group Q]
    (pi : G →* Q) (P : Subgroup G)
    (g : Subgroup.centralizer (P : Set G)) :
    (centralizerMap pi P g : Q) = pi (g : G) := rfl

/-- The literal centralizer restriction is onto; no abstract replacement
of either centralizer or of the original quotient is involved. -/
theorem centralizerMap_surjective
    {G Q : Type*} [Group G] [Finite G] [Group Q]
    (pi : G →* Q) (hpi : Function.Surjective pi)
    (hker : IsPGroup 2 pi.ker) (P : Sylow 3 G) :
    Function.Surjective (centralizerMap pi (P : Subgroup G)) := by
  intro q
  have hq : (q : Q) ∈ (Subgroup.centralizer (P : Set G)).map pi := by
    rw [map_centralizer_eq pi hpi hker P]
    exact q.property
  obtain ⟨g, hg, hgq⟩ := hq
  exact ⟨⟨g, hg⟩, Subtype.ext hgq⟩

end CoprimeTernaryCentralizerLift
end SymmetricSubgroupAsymptotics

end
