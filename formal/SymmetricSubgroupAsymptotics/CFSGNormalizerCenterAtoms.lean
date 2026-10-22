import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Subgroup.Center

/-! Intrinsic minimal subgroups in the actual centre of an actual
subgroup, normalized by its actual normalizer. Both the subgroup and
its centre atom are transported by the same isomorphism. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
variable {G G' : Type*} [Group G] [Group G']

def centerImage (P : Subgroup G) : Subgroup G := (Subgroup.center P).map P.subtype

def IsAtom (P H : Subgroup G) : Prop :=
  H ≠ ⊥ ∧ H ≤ centerImage P ∧
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (H : Set G) ∧
    ∀ J : Subgroup G, J ≠ ⊥ → J ≤ H →
      Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (J : Set G) → J = H

theorem map_centerImage (f : G ≃* G') (P : Subgroup G) :
    (centerImage P).map f.toMonoidHom = centerImage (P.map f.toMonoidHom) := by
  let e : P ≃* P.map f.toMonoidHom := f.subgroupMap P
  ext g
  constructor
  · rintro ⟨x, ⟨z, hz, hzx⟩, hxg⟩
    refine ⟨e z, (Subgroup.centerCongr e ⟨z, hz⟩).property, ?_⟩
    change f z.val = g
    exact (congrArg f hzx).trans hxg
  · rintro ⟨z, hz, hzg⟩
    let y : P := e.symm z
    have hy : y ∈ Subgroup.center P := ((Subgroup.centerCongr e).symm ⟨z, hz⟩).property
    refine ⟨y.val, ⟨y, hy, rfl⟩, ?_⟩
    have he := congrArg Subtype.val (e.apply_symm_apply z)
    change f y.val = z.val at he
    exact he.trans hzg

theorem map_isAtom (f : G ≃* G') (P H : Subgroup G) (h : IsAtom P H) :
    IsAtom (P.map f.toMonoidHom) (H.map f.toMonoidHom) := by
  let E : Subgroup G ≃o Subgroup G' := f.mapSubgroup
  have hnorm (J : Subgroup G) : E (Subgroup.normalizer (J : Set G)) =
      Subgroup.normalizer (E J : Set G') := Subgroup.map_equiv_normalizer_eq J f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hbot
    exact h.1 (E.injective (hbot.trans E.map_bot.symm))
  · have hh := E.monotone h.2.1
    change H.map f.toMonoidHom ≤ (centerImage P).map f.toMonoidHom at hh
    rwa [map_centerImage] at hh
  · have hh := E.monotone h.2.2.1
    rw [hnorm P, hnorm H] at hh
    exact hh
  · intro J' hJne hJle hJN
    let J : Subgroup G := E.symm J'
    have heJ : E J = J' := E.apply_symm_apply J'
    have hne : J ≠ ⊥ := by
      intro hbot
      exact hJne (heJ.symm.trans ((congrArg E hbot).trans E.map_bot))
    have hle : J ≤ H := by
      have hle' : J' ≤ E H := hJle
      have hh := E.symm.monotone hle'
      simpa only [E.symm_apply_apply] using hh
    have hN : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (J : Set G) := by
      have hh := hJN
      change Subgroup.normalizer (E P : Set G') ≤ Subgroup.normalizer (J' : Set G') at hh
      rw [← heJ, ← hnorm P, ← hnorm J] at hh
      have hs := E.symm.monotone hh
      simpa only [E.symm_apply_apply] using hs
    have hJ := h.2.2.2 J hne hle hN
    exact heJ.symm.trans (congrArg E hJ)

end SymmetricSubgroupAsymptotics.CFSGNormalizerCenterAtoms
