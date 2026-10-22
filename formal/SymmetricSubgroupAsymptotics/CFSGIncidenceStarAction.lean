import SymmetricSubgroupAsymptotics.CFSGIncidenceStarReconstruction
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-! The reconstructed point permutation is unique and therefore respects
composition. This constructs the actual action homomorphism, rather than
independently choosing incoherent point maps for each automorphism. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGIncidenceStarReconstruction
variable {P L : Type*} (rel : L → L → Prop)

def relationAut : Subgroup (Equiv.Perm L) where
  carrier := {f | ∀x y,rel (f x) (f y) ↔ rel x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro f g hf hg x y
    exact (hf (g x) (g y)).trans (hg x y)
  inv_mem' := by
    intro f hf x y
    have h := hf (f.symm x) (f.symm y)
    simpa only [f.apply_symm_apply] using h.symm

variable {rel} (G : Geometry (P:=P) rel)

def pointPerm (f : relationAut rel) : Equiv.Perm P :=
  Classical.choose (exists_point_equiv G f.val f.property)

theorem pointPerm_incidence (f : relationAut rel) (p : P) (t : L) :
    G.incident (pointPerm G f p) (f.val t) ↔ G.incident p t :=
  Classical.choose_spec (exists_point_equiv G f.val f.property) p t

def pointAction : relationAut rel →* Equiv.Perm P where
  toFun := pointPerm G
  map_one' := by
    apply point_equiv_unique G (f:=Equiv.refl L)
      (pointPerm_incidence G 1)
    · intro p t
      rfl
    · intro x y
      rfl
  map_mul' := by
    intro f g
    apply point_equiv_unique G (f:=(f*g).val) (pointPerm_incidence G (f*g))
    · intro p t
      change G.incident (pointPerm G f (pointPerm G g p)) (f.val (g.val t)) ↔ _
      rw [pointPerm_incidence,pointPerm_incidence]
    · exact (f*g).property

theorem pointAction_incidence (f : relationAut rel) (p : P) (t : L) :
    G.incident (pointAction G f p) (f.val t) ↔ G.incident p t :=
  pointPerm_incidence G f p t

theorem pointAction_injective
    (line_ext : ∀ {x y : L}, (∀p,G.incident p x ↔ G.incident p y) → x=y) :
    Function.Injective (pointAction G) := by
  intro f g hfg
  apply Subtype.ext
  apply Equiv.ext
  intro t
  apply line_ext
  intro p
  obtain ⟨q,rfl⟩ := (pointPerm G f).surjective p
  have he : pointPerm G f q=pointPerm G g q := congrArg (fun u:Equiv.Perm P=>u q) hfg
  calc
    G.incident (pointPerm G f q) (f.val t) ↔ G.incident q t := pointPerm_incidence G f q t
    _ ↔ G.incident (pointPerm G f q) (g.val t) := by
      rw [he]
      exact (pointPerm_incidence G g q t).symm

end SymmetricSubgroupAsymptotics.CFSGIncidenceStarReconstruction
