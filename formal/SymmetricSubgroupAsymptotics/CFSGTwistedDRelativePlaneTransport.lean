import SymmetricSubgroupAsymptotics.CFSGTwistedDNormalizedCommonNeighbours
import SymmetricSubgroupAsymptotics.CFSGTwistedDPlaneActionFaithful
import SymmetricSubgroupAsymptotics.CFSGCommonNeighbourRecognition

/-! The already constructed inner-automorphism action on actual planes
is the literal relative linear action. It transports the same finite
common-neighbour sets, without any new isometry recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePlaneTransport
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDFixedQuadraticAction
open CFSGTwistedDProjectiveUnipotent CFSGTwistedDSingularPlaneOrbit
open CFSGTwistedDPlaneFamilyAction CFSGTwistedDPlaneActionFaithful
open CFSGTwistedDPlaneAdjacencyActions CFSGTwistedDNormalizedCommonNeighbours

theorem innerPlane_action_map (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) (P : SingularPlanes s q) :
    (singularActionHom s q (MulAut.conj (projection s q g)) P).val =
      P.val.map (fixedLinearHom (s + 2) q g).toLinearMap := by
  have hp : P = singularPlane s q (representative s q P) :=
    Subtype.ext (representative_spec s q P)
  let h := representative s q P
  have hmul : (fixedLinearHom (s + 2) q (g * h)).toLinearMap =
      (fixedLinearHom (s + 2) q g).toLinearMap.comp
        (fixedLinearHom (s + 2) q h).toLinearMap := by
    apply LinearMap.ext
    intro x
    change fixedLinearHom (s + 2) q (g * h) x =
      fixedLinearHom (s + 2) q g (fixedLinearHom (s + 2) q h x)
    rw [map_mul]
    rfl
  have hact : (singularActionHom s q (MulAut.conj (projection s q g)) P).val =
      conjugateRootPlane s q (g * h) := by
    have he := congrArg (fun T : SingularPlanes s q =>
      (singularActionHom s q (MulAut.conj (projection s q g)) T).val) hp
    exact he.trans (congrArg Subtype.val (singularAction_inner_plane s q g h))
  calc
    _ = conjugateRootPlane s q (g * h) := hact
    _ = (conjugateRootPlane s q h).map (fixedLinearHom (s + 2) q g).toLinearMap := by
      change (standardRootPlane s q).map (fixedLinearHom (s + 2) q (g * h)).toLinearMap =
        ((standardRootPlane s q).map (fixedLinearHom (s + 2) q h).toLinearMap).map
          (fixedLinearHom (s + 2) q g).toLinearMap
      rw [← Submodule.map_comp, hmul]
    _ = P.val.map (fixedLinearHom (s + 2) q g).toLinearMap :=
      congrArg (fun T => T.map (fixedLinearHom (s + 2) q g).toLinearMap)
        (representative_spec s q P).symm

theorem inner_commonNeighbours_card (s : ℕ) (q : CFSG.PrimePower)
    (g : relativeRootGroup (s + 2) q) (P Q : SingularPlanes s q) :
    Nat.card (CommonNeighbours s q
      (singularActionHom s q (MulAut.conj (projection s q g)) P)
      (singularActionHom s q (MulAut.conj (projection s q g)) Q)) =
        Nat.card (CommonNeighbours s q P Q) :=
  CFSGCommonNeighbourRecognition.commonNeighbour_card
    (PlaneAdjacent s q) (singularActionHom s q (MulAut.conj (projection s q g)))
    (singularAction_preserves_adjacency s q (MulAut.conj (projection s q g))) P Q

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativePlaneTransport
