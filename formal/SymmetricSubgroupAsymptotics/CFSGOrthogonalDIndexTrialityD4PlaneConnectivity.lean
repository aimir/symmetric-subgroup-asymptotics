import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4NaturalPlaneAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4GeneratedOrbitPaths

/-! The original D4 quadratic singular-plane graph is connected.
Literal simple-root moves give genuine edges, closure induction gives
all actual elementary words, and the proved original two-plane orbit
supplies every original vertex. No building connectedness is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDIndexPlaneFamilyAction
open CFSGOrthogonalDIndexPlaneRootLine CFSGOrthogonalDIndexSingularPlaneOrbit
variable (K : Type) [Field K]

theorem original_root_reaches_elementary_image (g : elementaryRootGroup K 4) :
    Relation.ReflTransGen (originalPlaneAdjacent K) (originalRootPlane K)
      (naturalPlaneImage K g (originalRootPlane K)) := by
  apply CFSGOrthogonalDIndexTrialityD4GeneratedOrbitPaths.generated_orbit_reachable
    (elementaryRootGroup K 4)
    {u | ∃ neg i a, u = rootTransvection K 4 neg i a} rfl
    (naturalPlaneImage K) (naturalPlaneImage_one K) (naturalPlaneImage_mul K)
    (originalPlaneAdjacent K) (fun {_ _} => originalPlaneAdjacent_symm K)
    (fun h {_ _} => naturalPlaneImage_adjacent K h) (originalRootPlane K) ?_ g
  intro u hu
  obtain ⟨neg, i, a, rfl⟩ := hu
  rcases root_generator_plane_eq_or_adjacent K neg i a with he | ha
  · have hh : naturalPlaneImage K
        ⟨rootTransvection K 4 neg i a, rootTransvection_mem K 4 neg i a⟩
        (originalRootPlane K) = originalRootPlane K := Subtype.ext he.symm
    rw [hh]
  · exact Relation.ReflTransGen.single ha

theorem naturalPlaneImage_root_eq_conjugate (g : elementaryRootGroup K 4) :
    (naturalPlaneImage K g (originalRootPlane K)).val = conjugateRootPlane K 0 g := by
  change (rootPlane K).map (CFSGOrthogonalDIndexPositiveSpace.naturalLinearHom K 4 g).toLinearMap = _
  rw [rootPlane, Submodule.map_span, Set.image_pair]
  rfl

theorem original_root_reaches_every_plane (P : SingularPlanes K 0) :
    Relation.ReflTransGen (originalPlaneAdjacent K) (originalRootPlane K) P := by
  obtain ⟨g, hg⟩ := exists_conjugateRootPlane_of_singular K 0 P.val P.property.1 P.property.2
  have he : naturalPlaneImage K g (originalRootPlane K) = P :=
    Subtype.ext ((naturalPlaneImage_root_eq_conjugate K g).trans hg.symm)
  exact he ▸ original_root_reaches_elementary_image K g

theorem original_plane_graph_connected (P Q : SingularPlanes K 0) :
    Relation.ReflTransGen (originalPlaneAdjacent K) P Q :=
  (Relation.ReflTransGen.symmetric (fun _ _ => originalPlaneAdjacent_symm K)
    (original_root_reaches_every_plane K P)).trans (original_root_reaches_every_plane K Q)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4ResidualSpace
