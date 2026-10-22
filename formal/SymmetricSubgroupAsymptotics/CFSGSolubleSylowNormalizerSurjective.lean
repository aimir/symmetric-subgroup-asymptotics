import SymmetricSubgroupAsymptotics.SylowActualNormalizerLift
import Mathlib.GroupTheory.Solvable

/-! Solubility of the SAME Sylow normalizer descends through an actual
surjection, by the proved Frattini normalizer lifting theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerSurjective

theorem normalizer_soluble_map {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (P : Sylow p G) (hsol : IsSolvable (Subgroup.normalizer (P : Set G))) :
    IsSolvable (Subgroup.normalizer (((P : Subgroup G).map f) : Set H)) := by
  let N := Subgroup.normalizer (P : Set G)
  let M := Subgroup.normalizer (((P : Subgroup G).map f) : Set H)
  letI : IsSolvable N := hsol
  let fn : N →* M :=
    { toFun := fun x => ⟨f x.val,
        (P : Subgroup G).le_normalizer_map f ⟨x.val, x.property, rfl⟩⟩
      map_one' := Subtype.ext f.map_one
      map_mul' x y := Subtype.ext (f.map_mul x.val y.val) }
  have hfn : Function.Surjective fn := by
    intro y
    obtain ⟨x, hx, hxy⟩ := SylowActualNormalizerLift.exists_lift f hf P y.val y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  exact solvable_of_surjective (f := fn) hfn

theorem exists_sylow_soluble_normalizer_map {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (h : ∃ P : Sylow p G, IsSolvable (Subgroup.normalizer (P : Set G))) :
    ∃ Q : Sylow p H, IsSolvable (Subgroup.normalizer (Q : Set H)) := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P.mapSurjective (f := f) hf, normalizer_soluble_map f hf P hP⟩

end SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerSurjective
