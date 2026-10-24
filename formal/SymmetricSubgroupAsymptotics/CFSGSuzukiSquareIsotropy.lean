import SymmetricSubgroupAsymptotics.CFSGSuzukiAbsoluteTraceQuadratic
import SymmetricSubgroupAsymptotics.CFSGSuzukiSubgroupPrimeFieldLayers
import SymmetricSubgroupAsymptotics.QuadraticRadicalIsotropyCardinality
import SymmetricSubgroupAsymptotics.InvariantAnnihilatorOrbitIndex

/-! The actual square map bounds the first-coordinate image of every
centre-proper subgroup of Suzuki U. Arbitrary nonzero prime-field
functionals are normalized using actual thetaProduct bijectivity; the
subspace is never claimed linear over the Suzuki coefficient field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiSquareIsotropy
open CFSGSuzukiFieldParameters CFSGSuzukiTorus CFSGSuzukiUnipotent
open CFSGSuzukiAbsoluteTrace CFSGSuzukiAbsoluteTraceQuadratic
open CFSGSuzukiCentralExtensionLayers CFSGSuzukiSubgroupPrimeFieldLayers
open FieldFunctionalMultiplicationDuality QuadraticRadicalIsotropyCardinality

theorem scaled_trace_singular_card_le (m : ℕ) (c : Field m) (hc : c ≠ 0)
    (W : Submodule (ZMod 2) (Field m))
    (hW : ∀ a ∈ W, traceLinear m (c * (theta m a * a)) = 0) :
    Nat.card W ≤ 2 ^ m := by
  obtain ⟨t, ht⟩ := (thetaProduct_bijective m).surjective c
  have ht0 : t ≠ 0 := by
    intro he
    rw [he, thetaProduct, map_zero, zero_mul] at ht
    exact hc ht.symm
  let e : Field m ≃ₗ[ZMod 2] Field m :=
    (Units.mk0 t ht0).mulLeftLinearEquiv (ZMod 2) (Field m)
  let W' : Submodule (ZMod 2) (Field m) := W.map e.toLinearMap
  have hW' : ∀ x ∈ W', quadratic m x = 0 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    change traceLinear m ((t * a) * theta m (t * a)) = 0
    rw [(theta m).map_mul t a]
    have hid : (t * a) * (theta m t * theta m a) = c * (theta m a * a) := by
      rw [← ht]
      change (t * a) * (theta m t * theta m a) = (t * theta m t) * (theta m a * a)
      ring
    rw [hid]
    exact hW a ha
  let f : W → W' := fun a => ⟨e a.val, ⟨a.val, a.property, rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (e.injective (congrArg Subtype.val hab))
  calc
    Nat.card W ≤ Nat.card W' := Nat.card_le_card_of_injective f hf
    _ ≤ Nat.card (ZMod 2) ^ m := card_le_of_odd_dimension (quadratic m)
      (quadratic_radical_eq_bot m) m (field_finrank m) W' hW'
    _ = 2 ^ m := by rw [Nat.card_zmod]

theorem functional_singular_card_le (m : ℕ) (f : Module.Dual (ZMod 2) (Field m))
    (hf : f ≠ 0) (W : Submodule (ZMod 2) (Field m))
    (hW : ∀ a ∈ W, f (theta m a * a) = 0) : Nat.card W ≤ 2 ^ m := by
  obtain ⟨c, hc, _⟩ := exists_unique_coefficient (traceLinear m) (traceLinear_ne_zero m) f
  have hc0 : c ≠ 0 := by
    intro he
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [hc x, he, zero_mul, map_zero]
  apply scaled_trace_singular_card_le m c hc0 W
  intro a ha
  exact (hc (theta m a * a)).symm.trans (hW a ha)

theorem vectorSubspace_card_le (m : ℕ) (J : Subgroup (unipotentSubgroup m))
    (hJ : ¬(centralHom m).range ≤ J) : Nat.card (vectorSubspace m J) ≤ 2 ^ m := by
  have hC := centralSubspace_ne_top m J hJ
  have hz : ∃ z : Field m, z ∉ centralSubspace m J := by
    by_contra h
    apply hC
    apply top_unique
    intro z _
    exact not_not.mp (not_exists.mp h z)
  obtain ⟨z, hz⟩ := hz
  obtain ⟨f, hf⟩ := InvariantAnnihilatorOrbitIndex.exists_annihilator_nonzero_on
    (centralSubspace m J) z hz
  have hf0 : f.val ≠ 0 := by
    intro he
    apply hf
    rw [he, LinearMap.zero_apply]
  apply functional_singular_card_le m f.val hf0 (vectorSubspace m J)
  intro a ha
  exact ((Submodule.mem_dualAnnihilator f.val).mp f.property) _
    (square_mem_centralSubspace m J a ha)

end SymmetricSubgroupAsymptotics.CFSGSuzukiSquareIsotropy
