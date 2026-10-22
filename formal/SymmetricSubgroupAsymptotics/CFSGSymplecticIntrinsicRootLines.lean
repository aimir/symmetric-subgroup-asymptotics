import SymmetricSubgroupAsymptotics.CFSGSymplecticRootCommutation
import SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveOddRootRecognition
import Mathlib.Algebra.Group.Subgroup.Finite

/-! An actual projective natural-root line is recovered intrinsically
from commuting-root tests on any of its nonidentity elements. In odd
characteristic every abstract projective automorphism therefore maps
the original natural-root family to itself. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveOddRootRecognition
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
private theorem root_parameter_zero (r : ℕ) (hr : 0 < r) (v : Index (r + 1) → K) :
    projectiveNaturalRootHom r hr v (Multiplicative.ofAdd (0 : K)) = 1 :=
  (projectiveNaturalRootHom r hr v).map_one

omit [Finite K] in
private theorem root_vector_zero (r : ℕ) (hr : 0 < r) (a : K) :
    projectiveNaturalRootHom r hr (0 : Index (r + 1) → K) (Multiplicative.ofAdd a) = 1 := by
  change QuotientGroup.mk' (Subgroup.center (elementaryRootGroup K (r + 1)))
    (actualNaturalRootElement r hr 0 a) = 1
  have he : actualNaturalRootElement r hr (0 : Index (r + 1) → K) a = 1 := by
    apply elementary_eq_of_mulVec_eq
    intro x
    simp only [actualNaturalRootElement_apply, transvection_apply,
      pairing_zero_left, mul_zero, zero_smul, add_zero]
    exact (Matrix.one_mulVec x).symm
  rw [he, map_one]

def SameRootTests (r : ℕ) (hr : 0 < r) (A B : elementaryProjective K (r + 1)) : Prop :=
  ∀ T, IsProjectiveNaturalRootElement r hr T → (Commute A T ↔ Commute B T)

theorem sameRootTests_root_iff (r : ℕ) (hr : 0 < r)
    (v w : Index (r + 1) → K) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    SameRootTests r hr
      (projectiveNaturalRootHom r hr v (Multiplicative.ofAdd a))
      (projectiveNaturalRootHom r hr w (Multiplicative.ofAdd b)) ↔
      ∀ x, pairing (r + 1) v x = 0 ↔ pairing (r + 1) w x = 0 := by
  constructor
  · intro h x
    have hh := h (projectiveNaturalRootHom r hr x (Multiplicative.ofAdd 1)) ⟨x, 1, rfl⟩
    simpa only [projectiveNaturalRootElement_commute_iff r hr _ _ _ _ ha one_ne_zero,
      projectiveNaturalRootElement_commute_iff r hr _ _ _ _ hb one_ne_zero] using hh
  · intro h T hT
    obtain ⟨x, c, rfl⟩ := hT
    by_cases hc : c = 0
    · subst c
      rw [root_parameter_zero]
      simp only [Commute.one_right]
    · simpa only [projectiveNaturalRootElement_commute_iff r hr _ _ _ _ ha hc,
        projectiveNaturalRootElement_commute_iff r hr _ _ _ _ hb hc] using h x

omit [Finite K] in
theorem sameRootTests_map (r : ℕ) (hr : 0 < r)
    (f : MulAut (elementaryProjective K (r + 1)))
    (hroot : ∀ T, IsProjectiveNaturalRootElement r hr (f T) ↔
      IsProjectiveNaturalRootElement r hr T)
    {A B : elementaryProjective K (r + 1)} (h : SameRootTests r hr A B) :
    SameRootTests r hr (f A) (f B) := by
  intro T hT
  have hpre : IsProjectiveNaturalRootElement r hr (f.symm T) :=
    (hroot (f.symm T)).mp (by simpa only [f.apply_symm_apply] using hT)
  constructor
  · intro hAT
    have ha : Commute A (f.symm T) := by
      simpa only [f.symm_apply_apply] using hAT.map f.symm
    have hb := (h (f.symm T) hpre).mp ha
    simpa only [f.apply_symm_apply] using hb.map f
  · intro hBT
    have hb : Commute B (f.symm T) := by
      simpa only [f.symm_apply_apply] using hBT.map f.symm
    have ha := (h (f.symm T) hpre).mpr hb
    simpa only [f.apply_symm_apply] using ha.map f

theorem automorphism_maps_projectiveNaturalRootLine (p r : ℕ)
    [Fact p.Prime] [CharP K p] (hr : 0 < r) (htwo : (2 : K) ≠ 0)
    (f : MulAut (elementaryProjective K (r + 1)))
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    ∃ w : Index (r + 1) → K, w ≠ 0 ∧
      (projectiveNaturalRootLine r hr v).map f.toMonoidHom =
        projectiveNaturalRootLine r hr w := by
  let R := projectiveNaturalRootHom r hr v
  have hR : R (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h
    have he := (projectiveNaturalRootHom_injective r hr v hv)
      (h.trans R.map_one.symm)
    have hh := congrArg Multiplicative.toAdd he
    exact one_ne_zero hh
  have hroot := automorphism_isProjectiveNaturalRootElement_iff p r hr htwo f
  obtain ⟨w, b, hwb⟩ := (hroot (R (Multiplicative.ofAdd 1))).mpr ⟨v, 1, rfl⟩
  have hnon : f (R (Multiplicative.ofAdd 1)) ≠ 1 :=
    fun h => hR (f.injective (h.trans f.map_one.symm))
  have hb : b ≠ 0 := by
    intro hz
    subst b
    exact hnon (hwb.trans (root_parameter_zero r hr w))
  have hw : w ≠ 0 := by
    intro hz
    subst w
    exact hnon (hwb.trans (root_vector_zero r hr b))
  refine ⟨w, hw, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · rintro T ⟨u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := hu
    by_cases ha : a.toAdd = 0
    · have hz : R a = 1 := by
        change projectiveNaturalRootHom r hr v a = 1
        have ha' : a = Multiplicative.ofAdd (0 : K) := Multiplicative.toAdd.injective ha
        rw [ha', root_parameter_zero]
      rw [hz, map_one]
      exact (projectiveNaturalRootLine r hr w).one_mem
    · obtain ⟨x, c, hxc⟩ := (hroot (R a)).mpr ⟨v, a.toAdd, rfl⟩
      have hc : c ≠ 0 := by
        intro hc0
        subst c
        have hu0 : R a = 1 := f.injective
          ((hxc.trans (root_parameter_zero r hr x)).trans f.map_one.symm)
        have he := (projectiveNaturalRootHom_injective r hr v hv) (hu0.trans R.map_one.symm)
        exact ha (congrArg Multiplicative.toAdd he)
      have ht : SameRootTests r hr (R (Multiplicative.ofAdd 1)) (R a) :=
        (sameRootTests_root_iff r hr v v 1 a.toAdd one_ne_zero ha).mpr (fun _ => Iff.rfl)
      have hmap := sameRootTests_map r hr f hroot ht
      rw [hwb, hxc] at hmap
      have he : projectiveNaturalRootLine r hr w = projectiveNaturalRootLine r hr x := by
        rw [projectiveNaturalRootLine_eq_iff r hr w x hw]
        exact (same_pairing_zero_tests_iff (r + 1) w x hw).mp
          ((sameRootTests_root_iff r hr w x b c hb hc).mp hmap)
      change f (R a) ∈ projectiveNaturalRootLine r hr w
      rw [hxc, he]
      exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rw [Subgroup.card_map_of_injective f.injective,
      projectiveNaturalRootLine_card r hr v hv, projectiveNaturalRootLine_card r hr w hw]

end SymmetricSubgroupAsymptotics.CFSGSymplecticProjectiveOddRootRecognition
