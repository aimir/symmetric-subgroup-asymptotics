import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.Group

/-! Intersecting an actual Sylow with a subgroup containing an element
that lies in a unique conjugate Sylow again gives a Sylow. Its normalizer
embeds into the ambient Sylow normalizer. This supplies both conclusions
for literal fixed subgroups once uniqueness is proved geometrically. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGRegularElementSylowIntersection
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

def intersectionSylow (P : Sylow p G) (R : Subgroup G) (r : G)
    (hrP : r ∈ (P : Subgroup G)) (hrR : r ∈ R)
    (hreg : ∀ g : G, g⁻¹ * r * g ∈ (P : Subgroup G) →
      g ∈ Subgroup.normalizer (P : Set G)) : Sylow p R where
  toSubgroup := (P : Subgroup G).subgroupOf R
  isPGroup' := by
    let f : (P : Subgroup G).subgroupOf R →* (P : Subgroup G) :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply P.isPGroup'.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (P : Subgroup G) => z.val) h
  is_maximal' := by
    intro Q hQ hUQ
    have hmapP : IsPGroup p (Q.map R.subtype) := hQ.map R.subtype
    obtain ⟨S, hQS⟩ := hmapP.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
    have he : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (S : Subgroup G) := by
      have hh := congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
      simpa only [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using hh
    have hrS : r ∈ (S : Subgroup G) :=
      hQS ⟨⟨r, hrR⟩, hUQ hrP, rfl⟩
    rw [← he] at hrS
    obtain ⟨x, hx, hxr⟩ := hrS
    have hgr : g⁻¹ * r * g ∈ (P : Subgroup G) := by
      have hx' : g⁻¹ * r * g = x := by
        rw [← hxr]
        change g⁻¹ * (g * x * g⁻¹) * g = x
        group
      rw [hx']
      exact hx
    have hgN := hreg g hgr
    apply le_antisymm _ hUQ
    intro y hy
    have hyS := hQS (show y.val ∈ Q.map R.subtype from ⟨y, hy, rfl⟩)
    rw [← he] at hyS
    obtain ⟨z, hz, hzy⟩ := hyS
    change y.val ∈ (P : Subgroup G)
    rw [← hzy]
    exact (Subgroup.mem_normalizer_iff.mp hgN z).mp hz

theorem normalizer_intersection_soluble (P : Sylow p G) (R : Subgroup G) (r : G)
    (hrP : r ∈ (P : Subgroup G)) (hrR : r ∈ R)
    (hreg : ∀ g : G, g⁻¹ * r * g ∈ (P : Subgroup G) →
      g ∈ Subgroup.normalizer (P : Set G))
    [IsSolvable (Subgroup.normalizer (P : Set G))] :
    IsSolvable (Subgroup.normalizer
      (((P : Subgroup G).subgroupOf R) : Set R)) := by
  let V := (P : Subgroup G).subgroupOf R
  let NR := Subgroup.normalizer (V : Set R)
  let NG := Subgroup.normalizer (P : Set G)
  have hmap (x : NR) : x.val.val ∈ NG := by
    apply hreg
    have hxinv : x.val⁻¹ ∈ NR := NR.inv_mem x.property
    have hrV : (⟨r, hrR⟩ : R) ∈ V := hrP
    have hh := (Subgroup.mem_normalizer_iff.mp hxinv (⟨r, hrR⟩ : R)).mp hrV
    have hh' : x.val⁻¹ * (⟨r, hrR⟩ : R) * x.val ∈ V := by
      simpa only [inv_inv] using hh
    exact hh'
  let f : NR →* NG :=
    { toFun := fun x => ⟨x.val.val, hmap x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : NG => z.val) h
  exact solvable_of_solvable_injective (f := f) hf

end SymmetricSubgroupAsymptotics.CFSGRegularElementSylowIntersection
