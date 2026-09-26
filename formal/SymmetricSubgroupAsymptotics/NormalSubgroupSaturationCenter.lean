import SymmetricSubgroupAsymptotics.NormalSubgroupSaturationCommutators
import SymmetricSubgroupAsymptotics.FiniteQuotientDerivedIntersection

/-! Nonempty saturation also controls the actual quotient-center
preimage. The starting element need not belong to the original normal
subgroup: its first commutator belongs there, and all later original
commutators remain there by whole-ambient normality. -/
set_option autoImplicit false
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics

variable {G ι κ : Type*} [Group G]

theorem iteratedOriginalCommutator_mem_of_first
    (g : ι → G) (M : Subgroup G) [M.Normal] (x : G)
    (hfirst : ∀ i, ⁅x, g i⁆ ∈ M) (w : List ι) (hw : w ≠ []) :
    iteratedOriginalCommutator g x w ∈ M := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons i w => exact iteratedOriginalCommutator_mem g M ⁅x, g i⁆ (hfirst i) w

theorem originalCommutatorProduct_mem_of_first
    (g : ι → G) (M : Subgroup G) [M.Normal] (x : G)
    (hfirst : ∀ i, ⁅x, g i⁆ ∈ M) (words : List (List ι))
    (hne : ∀ w ∈ words, w ≠ []) :
    originalCommutatorProduct g x words ∈ M := by
  apply M.list_prod_mem
  intro y hy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
  exact iteratedOriginalCommutator_mem_of_first g M x hfirst w (hne w hw)

namespace NormalSubgroupSaturationCertificate

variable {D R : Subgroup G} {ambient : ι → G}
    {radicalGenerators : κ → G} {n : ℕ}
    (C : NormalSubgroupSaturationCertificate D R ambient radicalGenerators n)
include C

/-- An element of D central modulo M, but outside R, forces all of R
into M by its actual nonempty original commutator words. -/
theorem radical_le_of_center_mem_outside (hne : C.NonemptyWords)
    (M : Subgroup G) [M.Normal] (x : G)
    (hxD : x ∈ D) (hxR : x ∉ R) (hx : x ∈ quotientCenterPreimage M) :
    R ≤ M := by
  obtain ⟨i, hi⟩ := C.rows_cover x hxD
  have hout : C.inside i = false := by
    cases h : C.inside i with
    | false => rfl
    | true => exact False.elim (hxR (hi ▸ C.inside_mem i h))
  have hfirst : ∀ j, ⁅C.rows i, ambient j⁆ ∈ M := by
    intro j
    rw [hi]
    exact (mem_quotientCenterPreimage_iff_all_commutators M x).mp hx (ambient j)
  rw [← C.radical_full]
  apply (Subgroup.closure_le M).mpr
  rintro _ ⟨j, rfl⟩
  rw [← C.words_eq i hout j]
  exact originalCommutatorProduct_mem_of_first ambient M (C.rows i)
    hfirst (C.words i j) (hne i hout j)

/-- Unless M contains R, the original quotient-center preimage has no
D-element outside R. No subgroup-order or head premise is supplied. -/
theorem quotientCenterPreimage_inf_le (hne : C.NonemptyWords)
    (M : Subgroup G) [M.Normal] (hnot : ¬ R ≤ M) :
    quotientCenterPreimage M ⊓ D ≤ R := by
  intro x hx
  by_contra hxR
  exact hnot (C.radical_le_of_center_mem_outside hne M x hx.2 hxR hx.1)

theorem quotientCenterPreimage_le (hne : C.NonemptyWords)
    (M : Subgroup G) [M.Normal] (hnot : ¬ R ≤ M)
    (hcenter : quotientCenterPreimage M ≤ D) :
    quotientCenterPreimage M ≤ R := by
  intro x hx
  exact C.quotientCenterPreimage_inf_le hne M hnot ⟨hx, hcenter hx⟩

end NormalSubgroupSaturationCertificate
end SymmetricSubgroupAsymptotics
