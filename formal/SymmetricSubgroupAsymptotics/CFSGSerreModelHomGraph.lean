import SymmetricSubgroupAsymptotics.CFSGSerreModelRootGeneration
import SymmetricSubgroupAsymptotics.CFSGGeneratedActionRange

/-! A prescribed root graph is functional once the prescribed root images
are realized by an actual homomorphism of the ORIGINAL Model. The map
need not extend to an automorphism of the ambient general linear group.
This is suitable for exceptional isogenies as well as ordinary twists. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreModelHomGraph
open CFSG.Models.Chevalley CFSGSerreLocalNilpotence CFSGSerreModelRootGeneration
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]

def graphHom (φ : Model A K →* Model A K) : Model A K →* (Ambient A K × Ambient A K) where
  toFun g := (g.val,(φ g).val)
  map_one' := Prod.ext rfl (congrArg Subtype.val (map_one φ))
  map_mul' g h := Prod.ext rfl (congrArg Subtype.val (map_mul φ g h))

variable (perm : Fin n → Fin n) (exponent : Fin n → ℕ)
    (φ : Model A K →* Model A K)
    (hφ : ∀neg i t,φ (modelRoot A K neg i t)=
      modelRoot A K neg (perm i) (t^(exponent i)))
include hφ

theorem twistGraph_eq_range : twistGraph A K perm exponent=(graphHom A K φ).range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro gh ⟨neg,i,t,h1,h2⟩
    have h1' : gh.1=rootEquiv A K neg i t := by
      apply LinearEquiv.toLinearMap_injective
      exact h1
    have h2' : gh.2=rootEquiv A K neg (perm i) (t^(exponent i)) := by
      apply LinearEquiv.toLinearMap_injective
      exact h2
    refine ⟨modelRoot A K neg i t,?_⟩
    apply Prod.ext
    · exact h1'.symm
    · exact (congrArg Subtype.val (hφ neg i t)).trans h2'.symm
  · apply CFSGGeneratedActionRange.range_le_of_generators
      (rootSet A K) (rootSet_generate A K) (graphHom A K φ) (twistGraph A K perm exponent)
    rintro g ⟨neg,i,t,rfl⟩
    change ((modelRoot A K neg i t).val,(φ (modelRoot A K neg i t)).val)∈_
    rw [hφ]
    exact Subgroup.subset_closure ⟨neg,i,t,rfl,rfl⟩

theorem mem_twistGraph_model_iff (g h : Model A K) :
    (g.val,h.val)∈twistGraph A K perm exponent ↔ φ g=h := by
  rw [twistGraph_eq_range A K perm exponent φ hφ]
  constructor
  · rintro ⟨x,hx⟩
    have hfirst : x=g := Subtype.ext (congrArg Prod.fst hx)
    have hsecond : φ x=h := Subtype.ext (congrArg Prod.snd hx)
    exact hfirst ▸ hsecond
  · intro hh
    refine ⟨g,?_⟩
    change (g.val,(φ g).val)=(g.val,h.val)
    exact congrArg (fun x : Model A K => (g.val,x.val)) hh

theorem mem_fixedSubgroup_model_iff (g : Model A K) :
    g.val∈fixedSubgroup A K perm exponent ↔ φ g=g := by
  change (g.val∈subgroup A K ∧ (g.val,g.val)∈twistGraph A K perm exponent) ↔ _
  rw [mem_twistGraph_model_iff A K perm exponent φ hφ]
  exact ⟨fun h=>h.2,fun h=>⟨g.property,h⟩⟩

end SymmetricSubgroupAsymptotics.CFSGSerreModelHomGraph
