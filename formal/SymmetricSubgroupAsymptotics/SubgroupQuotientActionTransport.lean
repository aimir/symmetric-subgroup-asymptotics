import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Action.End

/-! Subgroup alignment transports along an actual intertwining quotient
map. All map composition is proved over abstract groups, so concrete
field/model aliases do not have to normalize inside subgroup rewrites.
Neither surjectivity nor any automorphism lifting is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SubgroupQuotientActionTransport
variable {G H : Type*} [Group G] [Group H]

theorem map_alignment (pi : G →* H) (u : MulAut G) (v : MulAut H)
    (hintertwine : ∀ x : G, v (pi x) = pi (u x))
    (P Q : Subgroup G) (A B : Subgroup H)
    (hP : P.map pi = A) (hQ : Q.map pi = B)
    (halign : P.map u.toMonoidHom = Q) : A.map v.toMonoidHom = B := by
  have he : v.toMonoidHom.comp pi = pi.comp u.toMonoidHom := by
    ext x
    exact hintertwine x
  calc
    A.map v.toMonoidHom = (P.map pi).map v.toMonoidHom :=
      congrArg (fun T : Subgroup H => T.map v.toMonoidHom) hP.symm
    _ = (P.map u.toMonoidHom).map pi := by
      rw [Subgroup.map_map, he, ← Subgroup.map_map]
    _ = Q.map pi := congrArg (fun T : Subgroup G => T.map pi) halign
    _ = B := hQ

end SymmetricSubgroupAsymptotics.SubgroupQuotientActionTransport
