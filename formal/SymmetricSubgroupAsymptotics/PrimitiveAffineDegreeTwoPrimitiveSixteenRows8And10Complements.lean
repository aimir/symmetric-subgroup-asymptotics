import SymmetricSubgroupAsymptotics.TernaryPlaneDihedralAffineNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations

/-! The original row-eight and row-ten linear groups are explicit images
of the ternary affine models. Both their normal-generator bounds and their
irreducibility on the original four-bit space are proved here. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10Complements

open PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10LinearRelations

def linearGenerators8 : Fin 3 → LinearGroup := ![a, b, c]
def linearGenerators10 : Fin 4 → LinearGroup := ![a, b, s, t]
abbrev R8 : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators8)
abbrev R10 : Subgroup LinearGroup := Subgroup.closure (Set.range linearGenerators10)

theorem a_mem8 : a ∈ R8 := Subgroup.subset_closure ⟨0, rfl⟩
theorem b_mem8 : b ∈ R8 := Subgroup.subset_closure ⟨1, rfl⟩
theorem c_mem8 : c ∈ R8 := Subgroup.subset_closure ⟨2, rfl⟩
theorem a_mem10 : a ∈ R10 := Subgroup.subset_closure ⟨0, rfl⟩
theorem b_mem10 : b ∈ R10 := Subgroup.subset_closure ⟨1, rfl⟩
theorem s_mem10 : s ∈ R10 := Subgroup.subset_closure ⟨2, rfl⟩
theorem t_mem10 : t ∈ R10 := Subgroup.subset_closure ⟨3, rfl⟩

theorem R8_le_R10 : R8 ≤ R10 := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact a_mem10
  · exact b_mem10
  · exact R10.mul_mem t_mem10 s_mem10

/-- Projection onto the fixed plane of `a*b`; the other plane is
interchanged with it by the original generator `c`. -/
def projection (x : Vector) : Vector := x + (a * b) x + ((a * b) ^ 2) x

def seed (x : Vector) : Vector := if projection x = 0 then c x else projection x

def orbitBasis (x : Vector) : Fin 4 → Vector :=
  ![seed x, a (seed x), c (seed x), a (c (seed x))]

def orbitCombination (x : Vector) (k : Fin 16) : Vector :=
  ∑ i : Fin 4, if k.val.testBit i.val then orbitBasis x i else 0

/-- Only fifteen nonzero four-bit inputs and sixteen coefficient masks
are involved; there is no group or normal-subgroup enumeration. -/
theorem orbit_spans : ∀ x : Vector, x ≠ 0 → ∀ y : Vector,
    ∃ k : Fin 16, orbitCombination x k = y := by
  decide +kernel

theorem irreducible8 : AffineModel.Irreducible R8 := by
  intro S hS
  by_cases hbot : S = ⊥
  · exact Or.inl hbot
  right
  have hx : ∃ x ∈ S, x ≠ 0 := by
    by_contra h
    push Not at h
    apply hbot
    apply le_antisymm _ bot_le
    intro x hx
    exact AddSubgroup.mem_bot.mpr (h x hx)
  obtain ⟨x, hx, hx0⟩ := hx
  have hp : projection x ∈ S :=
    S.add_mem (S.add_mem hx (hS (a * b) (R8.mul_mem a_mem8 b_mem8) x hx))
      (hS ((a * b) ^ 2) (R8.pow_mem (R8.mul_mem a_mem8 b_mem8) 2) x hx)
  have hs : seed x ∈ S := by
    unfold seed
    split
    · exact hS c c_mem8 x hx
    · exact hp
  have hb : ∀ i : Fin 4, orbitBasis x i ∈ S := by
    intro i
    fin_cases i
    · exact hs
    · exact hS a a_mem8 _ hs
    · exact hS c c_mem8 _ hs
    · exact hS a a_mem8 _ (hS c c_mem8 _ hs)
  apply top_unique
  intro y _hy
  obtain ⟨k, hk⟩ := orbit_spans x hx0 y
  rw [← hk]
  unfold orbitCombination
  apply S.sum_mem
  intro i _hi
  split
  · exact hb i
  · exact S.zero_mem

theorem irreducible10 : AffineModel.Irreducible R10 := by
  intro S hS
  exact irreducible8 S (fun r hr x hx => hS r (R8_le_R10 hr) x hx)

abbrev CoreVector := TernaryPlaneDihedralAffineNormalGenerators.Vector
abbrev C4 := TernaryPlaneDihedralAffineNormalGenerators.C4
abbrev ModelFour := TernaryPlaneDihedralAffineNormalGenerators.ModelFour
abbrev ModelEight := TernaryPlaneDihedralAffineNormalGenerators.ModelEight

/-- The two commuting original order-three maps are the actual ternary
translation image. -/
def coreTranslationMap : Multiplicative CoreVector →* LinearGroup where
  toFun v := a ^ (v.toAdd 0).val * b ^ (v.toAdd 1).val
  map_one' := by simp
  map_mul' := by
    intro v w
    apply LinearEquiv.ext
    intro x
    revert v w x
    decide +kernel

def coreRotationMap : C4 →* LinearGroup where
  toFun i := c ^ i.toAdd.val
  map_one' := rfl
  map_mul' := by
    intro i j
    apply LinearEquiv.ext
    intro x
    revert i j x
    decide +kernel

def coreDihedralMap : DihedralGroup 4 →* LinearGroup where
  toFun
    | .r i => c ^ i.val
    | .sr i => s * c ^ i.val
  map_one' := rfl
  map_mul' := by
    rintro (i | i) (j | j) <;>
      apply LinearEquiv.ext <;> intro x <;> revert i j x <;> decide +kernel

def ternaryAction8 : ModelFour →* LinearGroup :=
  SemidirectProduct.lift coreTranslationMap coreRotationMap (by
    intro u
    apply MonoidHom.ext
    intro v
    apply LinearEquiv.ext
    intro x
    revert u v x
    decide +kernel)

def ternaryAction10 : ModelEight →* LinearGroup :=
  SemidirectProduct.lift coreTranslationMap coreDihedralMap (by
    intro u
    apply MonoidHom.ext
    intro v
    apply LinearEquiv.ext
    intro x
    revert u v x
    decide +kernel)

theorem coreTranslationMap_e0 :
    coreTranslationMap (Multiplicative.ofAdd TernaryPlaneDihedralAffineNormalGenerators.e0) = a := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

theorem coreTranslationMap_e1 :
    coreTranslationMap (Multiplicative.ofAdd TernaryPlaneDihedralAffineNormalGenerators.e1) = b := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

theorem coreRotationMap_one : coreRotationMap (Multiplicative.ofAdd 1) = c := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

theorem coreDihedralMap_sr_zero : coreDihedralMap (.sr 0) = s := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

theorem coreDihedralMap_sr_three : coreDihedralMap (.sr 3) = t := by
  apply LinearEquiv.ext
  intro x
  revert x
  decide +kernel

theorem ternaryAction8_range : ternaryAction8.range = R8 := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    change (a ^ (g.left.toAdd 0).val * b ^ (g.left.toAdd 1).val) *
      c ^ g.right.toAdd.val ∈ R8
    exact R8.mul_mem (R8.mul_mem (R8.pow_mem a_mem8 _) (R8.pow_mem b_mem8 _))
      (R8.pow_mem c_mem8 _)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · refine ⟨SemidirectProduct.inl
        (Multiplicative.ofAdd TernaryPlaneDihedralAffineNormalGenerators.e0), ?_⟩
      rw [ternaryAction8, SemidirectProduct.lift_inl]
      exact coreTranslationMap_e0
    · refine ⟨SemidirectProduct.inl
        (Multiplicative.ofAdd TernaryPlaneDihedralAffineNormalGenerators.e1), ?_⟩
      rw [ternaryAction8, SemidirectProduct.lift_inl]
      exact coreTranslationMap_e1
    · refine ⟨SemidirectProduct.inr (Multiplicative.ofAdd 1), ?_⟩
      rw [ternaryAction8, SemidirectProduct.lift_inr]
      exact coreRotationMap_one

theorem ternaryAction10_range : ternaryAction10.range = R10 := by
  apply le_antisymm
  · rintro _ ⟨g, rfl⟩
    change coreTranslationMap g.left * coreDihedralMap g.right ∈ R10
    apply R10.mul_mem
    · exact R10.mul_mem (R10.pow_mem a_mem10 _) (R10.pow_mem b_mem10 _)
    · have hc : c ∈ R10 := R10.mul_mem t_mem10 s_mem10
      cases g.right with
      | r i => exact R10.pow_mem hc _
      | sr i => exact R10.mul_mem s_mem10 (R10.pow_mem hc _)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · refine ⟨SemidirectProduct.inl
        (Multiplicative.ofAdd TernaryPlaneDihedralAffineNormalGenerators.e0), ?_⟩
      rw [ternaryAction10, SemidirectProduct.lift_inl]
      exact coreTranslationMap_e0
    · refine ⟨SemidirectProduct.inl
        (Multiplicative.ofAdd TernaryPlaneDihedralAffineNormalGenerators.e1), ?_⟩
      rw [ternaryAction10, SemidirectProduct.lift_inl]
      exact coreTranslationMap_e1
    · refine ⟨SemidirectProduct.inr (.sr 0), ?_⟩
      rw [ternaryAction10, SemidirectProduct.lift_inr]
      exact coreDihedralMap_sr_zero
    · refine ⟨SemidirectProduct.inr (.sr 3), ?_⟩
      rw [ternaryAction10, SemidirectProduct.lift_inr]
      exact coreDihedralMap_sr_three

def complementMap8 : ModelFour →* R8 :=
  (MulEquiv.subgroupCongr ternaryAction8_range).toMonoidHom.comp
    ternaryAction8.rangeRestrict

def complementMap10 : ModelEight →* R10 :=
  (MulEquiv.subgroupCongr ternaryAction10_range).toMonoidHom.comp
    ternaryAction10.rangeRestrict

theorem complementMap8_surjective : Function.Surjective complementMap8 :=
  (MulEquiv.subgroupCongr ternaryAction8_range).surjective.comp
    ternaryAction8.rangeRestrict_surjective

theorem complementMap10_surjective : Function.Surjective complementMap10 :=
  (MulEquiv.subgroupCongr ternaryAction10_range).surjective.comp
    ternaryAction10.rangeRestrict_surjective

theorem normal_generating_pairs8 :
    ∀ N : Subgroup R8, N.Normal →
      ∃ x : Fin 2 → R8, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective complementMap8 complementMap8_surjective
    TernaryPlaneDihedralAffineNormalGenerators.modelFour_normal_generating_pairs

theorem normal_generating_pairs10 :
    ∀ N : Subgroup R10, N.Normal →
      ∃ x : Fin 2 → R10, Subgroup.normalClosure (Set.range x) = N :=
  normal_generating_tuples_of_surjective complementMap10 complementMap10_surjective
    TernaryPlaneDihedralAffineNormalGenerators.modelEight_normal_generating_pairs

end PrimitiveAffineDegreeTwoPrimitiveSixteenRows8And10Complements
end SymmetricSubgroupAsymptotics

end
