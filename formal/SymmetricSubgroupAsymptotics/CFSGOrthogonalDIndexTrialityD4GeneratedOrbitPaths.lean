import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Logic.Relation

/-! Generator edges imply orbit connectedness for an actual generated subgroup. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4GeneratedOrbitPaths
variable {G X : Type*} [Group G]

theorem generated_orbit_reachable (H : Subgroup G) (S : Set G)
    (hgen : Subgroup.closure S = H) (act : H → X → X)
    (hone : ∀ x, act 1 x = x)
    (hmul : ∀ g h x, act (g * h) x = act g (act h x))
    (R : X → X → Prop) (hsym : ∀ {x y}, R x y → R y x)
    (hact : ∀ g {x y}, R x y → R (act g x) (act g y))
    (x : X) (hstep : ∀ (g : G) (hg : g ∈ S),
      Relation.ReflTransGen R x (act ⟨g, hgen ▸ Subgroup.subset_closure hg⟩ x))
    (g : H) : Relation.ReflTransGen R x (act g x) := by
  let J : Subgroup H :=
    { carrier := {g | Relation.ReflTransGen R x (act g x)}
      one_mem' := by
        change Relation.ReflTransGen R x (act 1 x)
        rw [hone]
      mul_mem' := by
        intro g h hg hh
        change Relation.ReflTransGen R x (act (g * h) x)
        rw [hmul]
        exact hg.trans (Relation.ReflTransGen.lift (act g) (fun _ _ => hact g) hh)
      inv_mem' := by
        intro g hg
        have hh := Relation.ReflTransGen.lift (act g⁻¹) (fun _ _ => hact g⁻¹) hg
        have hc : act g⁻¹ (act g x) = x := by rw [← hmul, inv_mul_cancel, hone]
        rw [hc] at hh
        exact Relation.ReflTransGen.symmetric (fun _ _ => hsym) hh }
  have hclosure : Subgroup.closure S ≤ J.map H.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    exact ⟨⟨a, hgen ▸ Subgroup.subset_closure ha⟩, hstep a ha, rfl⟩
  have hle : H ≤ J.map H.subtype := hgen ▸ hclosure
  obtain ⟨j, hj, he⟩ := hle g.property
  have he' : j = g := Subtype.ext he
  exact he' ▸ hj

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4GeneratedOrbitPaths
