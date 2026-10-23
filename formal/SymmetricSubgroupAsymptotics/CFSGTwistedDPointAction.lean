import SymmetricSubgroupAsymptotics.CFSGTwistedDPointStars
import SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneActionFaithful

/-! A coherent faithful action of the SAME original twisted-D model's
automorphism group on all actual fixed-field singular points. The action
is reconstructed from intrinsic root subgroups, with no projective-
automorphism lift or polar-action hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDPointAction
open CFSGTwistedDPointStars CFSGTwistedDPlaneFamilyAction
open CFSGTwistedDPlaneActionFaithful CFSGTwistedDProjectiveUnipotent
open CFSGTwistedDR11CommonNeighbours CFSGTwistedDR11Recognition
open CFSGTwistedDRelativeProjectiveModel CFSGIncidenceStarReconstruction

def relationActionHom (s : ℕ) (q : CFSG.PrimePower) :
    MulAut (Projective s q) →* relationAut (IntersectingNonadjacent s q) where
  toFun f := ⟨singularActionHom s q f, singularAction_preserves_R11 s q f⟩
  map_one' := Subtype.ext ((singularActionHom s q).map_one)
  map_mul' f g := Subtype.ext ((singularActionHom s q).map_mul f g)

def projectivePointActionHom (s : ℕ) (q : CFSG.PrimePower) :
    MulAut (Projective s q) →* Equiv.Perm (SingularPoints s q) :=
  (pointAction (pointStarGeometry s q)).comp (relationActionHom s q)

theorem projectivePointAction_incidence (s : ℕ) (q : CFSG.PrimePower)
    (f : MulAut (Projective s q)) (U : SingularPoints s q) (P : SingularPlanes s q) :
    (projectivePointActionHom s q f U).val ≤ (singularActionHom s q f P).val ↔ U.val ≤ P.val :=
  pointAction_incidence (pointStarGeometry s q) (relationActionHom s q f) U P

theorem projectivePointActionHom_injective (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (Projective s q)] : Function.Injective (projectivePointActionHom s q) := by
  intro f g he
  have hr := pointStarAction_injective s q he
  apply singularActionHom_injective s q
  exact congrArg Subtype.val hr

def originalPointActionHom (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    MulAut (CFSG.Models.TwistedD (s + 4) q) →*
      Equiv.Perm (SingularPoints s q) :=
  (projectivePointActionHom s q).comp
    (MulAut.congr (originalRelativeProjectiveEquiv s q)).toMonoidHom

theorem originalPointActionHom_injective (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)] :
    Function.Injective (originalPointActionHom s q) := by
  let e := originalRelativeProjectiveEquiv s q
  letI : IsSimpleGroup (Projective s q) := e.symm.isSimpleGroup
  exact (projectivePointActionHom_injective s q).comp (MulAut.congr e).injective

end SymmetricSubgroupAsymptotics.CFSGTwistedDPointAction
