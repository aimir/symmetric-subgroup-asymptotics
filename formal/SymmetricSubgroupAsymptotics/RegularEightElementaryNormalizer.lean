import SymmetricSubgroupAsymptotics.RegularBinaryThreeAffineCoverage
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T3
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.NormNum

/-! The original regular8T3 subgroup has explicit E8 coordinates. Every
actual overgroup in its normalizer therefore has one of15 fixed affine
point actions, without primitiveness or any abstract row correspondence. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.RegularEightElementaryNormalizer
open BinaryThreeAffineRowActions

abbrev H : Subgroup Ambient := Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)

def element (v : Translation) : Ambient :=
  BinaryMenuCayley8T3.generators 0 ^ (v.toAdd 0).val *
    BinaryMenuCayley8T3.generators 1 ^ (v.toAdd 1).val *
    BinaryMenuCayley8T3.generators 2 ^ (v.toAdd 2).val

theorem element_mem (v : Translation) : element v ∈ H :=
  H.mul_mem (H.mul_mem
    (H.pow_mem (Subgroup.subset_closure (Set.mem_range_self 0)) _)
    (H.pow_mem (Subgroup.subset_closure (Set.mem_range_self 1)) _))
    (H.pow_mem (Subgroup.subset_closure (Set.mem_range_self 2)) _)

def hom : Translation →* H where
  toFun v := ⟨element v,element_mem v⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    revert x
    decide +kernel
  map_mul' v w := by
    have h : ∀ (v w : Translation) (x : Fin 8),
        element (v*w) x = (element v * element w) x := by decide +kernel
    apply Subtype.ext
    exact Equiv.ext (h v w)

theorem hom_injective : Function.Injective hom := by
  have h : ∀ (v w : Translation), element v 0 = element w 0 →
      ∀ i : Fin 3,v.toAdd i = w.toAdd i := by decide +kernel
  intro v w he
  apply Multiplicative.toAdd.injective
  apply funext
  apply h v w
  exact congrArg (fun g : H => g.val 0) he

theorem hom_bijective : Function.Bijective hom := by
  letI : Fintype H := Fintype.ofFinite H
  apply (Fintype.bijective_iff_injective_and_card hom).mpr
  refine ⟨hom_injective,?_⟩
  have hH : Fintype.card H = 8 := by
    simpa only [Nat.card_eq_fintype_card] using BinaryMenuCayley8T3.exact_card
  rw [hH]
  norm_num [Translation,BinaryThreeAffineRowActions.Vector]

def chart : Translation ≃* H := MulEquiv.ofBijective hom hom_bijective

theorem regular : ∀ x y : Fin 8,∃! v : H,v.val x = y := by
  have hs : ∀ x y : Fin 8,∃ v : Translation,element v x = y := by decide +kernel
  have hi : ∀ (x : Fin 8) (v w : Translation),element v x = element w x →
      ∀ i : Fin 3,v.toAdd i = w.toAdd i := by decide +kernel
  intro x y
  obtain ⟨v,hv⟩ := hs x y
  refine ⟨chart v,hv,?_⟩
  intro w hw
  obtain ⟨z,rfl⟩ := chart.surjective w
  apply congrArg chart
  apply Multiplicative.toAdd.injective
  apply funext
  exact hi x z v (hw.trans hv.symm)

variable (U : Subgroup Ambient) (hHU : H ≤ U) (hUN : U ≤ Subgroup.normalizer H)

def profile : PrimitiveAffineProfile U (Fin 8) where
  p := 2
  p_prime := by decide
  V := H.subgroupOf U
  V_normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHU).mpr hUN
  V_pgroup := by
    apply IsPGroup.of_card (n := 3)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHU).toEquiv]
    exact BinaryMenuCayley8T3.exact_card
  regular x y := by
    let e : H.subgroupOf U ≃* H := Subgroup.subgroupOfEquivOfLe hHU
    obtain ⟨v,hv,hunique⟩ := regular x y
    refine ⟨e.symm v,?_,?_⟩
    · change (e (e.symm v)).val x = y
      rw [e.apply_symm_apply]
      exact hv
    · intro w hw
      apply e.injective
      rw [e.apply_symm_apply]
      apply hunique
      exact hw

def profileChart : (profile U hHU hUN).V ≃* Translation :=
  (Subgroup.subgroupOfEquivOfLe hHU).trans chart.symm

include hHU hUN in
theorem complete : ∃ i : Fin 15,∃ c : Ambient,
    MulAut.conj c • U = BinaryThreeAffineRowActions.rows i := by
  obtain ⟨i,c,hc⟩ := RegularBinaryThreeAffineCoverage.complete
    (profile U hHU hUN) 0 (profileChart U hHU hUN)
  exact ⟨i,c,hc⟩

end SymmetricSubgroupAsymptotics.RegularEightElementaryNormalizer
end
