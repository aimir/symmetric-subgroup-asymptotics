import SymmetricSubgroupAsymptotics.BinaryReducibleLinearClassBound
import SymmetricSubgroupAsymptotics.AbelianSemidirectPlaneKernelClassBound
import SymmetricSubgroupAsymptotics.BinarySmallElementSemidirectClassBound
import Mathlib.Algebra.Field.ZMod

/-! A genuine nonzero proper translation intersection is automatically a
prime-field submodule and is invariant under the original subgroup's
OWN projected group. That reducible projected action has at most five
classes; the actual kernel has order at most four, giving twenty classes.
No full-field closure or splitness of the original subgroup is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryProperIntersectionSemidirectClassBound
open BinaryFiveElementSemidirectClassBound (automorphismLinear automorphismLinear_injective)

variable {N G : Type} [CommGroup N] [Group G] [Finite N] [Finite G]
    {p : ℕ} [Fact p.Prime] [Module (ZMod p) (Additive N)]

theorem class_card_le_twenty (hp : p = 2) (hN : Nat.card N = 8)
    (φ : G →* MulAut N) (hφ : Function.Injective φ) (L : Subgroup (N ⋊[φ] G))
    (hbot : L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] G)) ≠ ⊥)
    (htop : L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] G)) ≠ ⊤) :
    Nat.card (ConjClasses L) ≤ 20 := by
  letI : Finite (N ⋊[φ] G) := Finite.of_equiv (N × G) SemidirectProduct.equivProd.symm
  let K := L.comap (SemidirectProduct.inl : N →* (N ⋊[φ] G))
  let π : L →* G := (SemidirectProduct.rightHom : (N ⋊[φ] G) →* G).comp L.subtype
  let R := π.range
  let ψ : R →* MulAut N := φ.comp R.subtype
  let ρ : R →* (Additive N ≃ₗ[ZMod p] Additive N) :=
    (automorphismLinear (N := N) (p := p)).comp ψ
  let eW : Subgroup N ≃o Submodule (ZMod p) (Additive N) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule p)
  let W := eW K
  have hWbot : W ≠ ⊥ := by
    intro he
    exact hbot (eW.injective (he.trans eW.map_bot.symm))
  have hWtop : W ≠ ⊤ := by
    intro he
    exact htop (eW.injective (he.trans eW.map_top.symm))
  have hρ : Function.Injective ρ :=
    (automorphismLinear_injective (N := N) (p := p)).comp
      (hφ.comp Subtype.val_injective)
  have hstable (q : R) (v : Additive N) (hv : v ∈ W) : ρ q v ∈ W := by
    change v.toMul ∈ K at hv
    change φ q.val v.toMul ∈ K
    exact (AbelianSemidirectPlaneKernelClassBound.projected_preserves_intersection
      φ L q v.toMul).mpr hv
  have hK : Nat.card (ZMod p) = 2 := (Nat.card_zmod p).trans hp
  have hA : Nat.card (Additive N) = 8 := hN
  have hclasses : Nat.card (ConjClasses R) ≤ 5 :=
    BinaryReducibleLinearClassBound.class_card_le_five hK hA ρ hρ W hWbot hWtop hstable
  have hKcard : Nat.card K ≤ 4 :=
    BinarySmallElementSemidirectClassBound.proper_subgroup_card_le 3
      (by simpa using hN) K htop
  have hker : Nat.card (ConjClasses π.ker) ≤ 4 :=
    (Nat.card_le_card_of_surjective (@ConjClasses.mk π.ker _) ConjClasses.mk_surjective).trans
      ((AbelianSemidirectSubgroupCentralizerBound.kernel_card_le_intersection φ L).trans hKcard)
  exact (conjugacyClass_card_le_kernel_mul_range π).trans
    (by simpa using Nat.mul_le_mul hker hclasses)

end SymmetricSubgroupAsymptotics.BinaryProperIntersectionSemidirectClassBound
