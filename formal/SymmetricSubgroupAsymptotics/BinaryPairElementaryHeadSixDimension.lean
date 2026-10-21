import SymmetricSubgroupAsymptotics.BinaryBooleanFourActualHeadSixDimension
import SymmetricSubgroupAsymptotics.BinaryDegreeThirtyTwoRankNineElementaryTop

/-! Head six forces eleven actual dimensions for every original normal
axis of an elementary sixteen-point top. No pure polynomial template is
substituted for the original axis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X] (F : BinaryPairFrame U (Fin 16))

theorem elementary_top_axis_finrank_ge_eleven_of_normalGen_six
    (hU : IsPGroup 2 U) (hpow : ∀ t : F.top.range, t ^ 2 = 1)
    (B : Subgroup U) [B.Normal] (hB : B ≤ F.top.ker)
    (hhead : 6 ≤ MarkedC4.normalGen B) :
    11 ≤ Module.finrank (ZMod 2) (F.ambientAxis B) := by
  letI elementaryHeadSix_primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI elementaryHeadSix_topTransitive : MulAction.IsPretransitive F.top.range (Fin 16) :=
    F.top_pretransitive
  have hTop := F.top_isPGroup hU
  obtain ⟨E₀⟩ := transitiveBinaryPairFrame_nonempty 3 F.top.range hTop
    (by norm_num only [Nat.card_fin])
  obtain ⟨E, hzero, hH, hK⟩ := E₀.exists_original_elementary_zero_frame hTop hpow
  have hreg (j : Fin 3) : BinaryMenuCayley8T3.generators j ∈ E.top.range := by
    rw [hH]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hconst : (fun _ : Fin 8 => (1 : ZMod 2)) ∈ E.kernelSpace := by
    rw [hK]
    simp only [BinaryCoordinateSpace.mem_iff]
    decide +kernel
  let e := E.commonBooleanPointLabels
  have htranslations : ∀ i : Fin 4, ∃ t : F.top.range,
      ∀ j, t⁻¹ • e.symm j = e.symm (flipIndex i j) := by
    intro i
    let t := E.commonTranslationRow hzero hreg hconst i
    have hf (x : Fin 16) : e (t.val x) = flipIndex i (e x) :=
      E.commonTranslationRow_pointLabels hzero hreg hconst i x
    refine ⟨t, ?_⟩
    intro j
    apply t.val.injective
    change t.val (t.val.symm (e.symm j)) = t.val (e.symm (flipIndex i j))
    rw [Equiv.apply_symm_apply]
    apply e.injective
    rw [hf, Equiv.apply_symm_apply, Equiv.apply_symm_apply, flipIndex_involutive]
  let W := F.axisNaturalSubrepresentation B
  have hh : 6 ≤ Module.finrank (ZMod 2)
      (W.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) := by
    rw [representationHead_finrank_eq_coinvariants, ← F.axisNatural_normalGen B hB hU]
    exact hhead
  exact boolean_four_actual_translation_submodule_finrank_ge_eleven_of_head_six
    W e htranslations hh

end SymmetricSubgroupAsymptotics.BinaryPairFrame
