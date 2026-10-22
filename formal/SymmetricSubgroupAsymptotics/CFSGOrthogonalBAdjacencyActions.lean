import SymmetricSubgroupAsymptotics.CFSGOrthogonalBRootPlaneAdjacency
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularPlaneAction

/-! The actual original and centre-quotient B automorphism actions
preserve the exact polar-line adjacency relation. Quotient transport
uses the proved original odd-B centre equivalence, not an abstract lift
hypothesis. All original natural plane labels remain unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent
variable {K : Type} [Field K] [Finite K]

theorem rootAdjacent_map (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryRootGroup K (s + 3)))
    (L M : Subgroup (elementaryRootGroup K (s + 3))) (h : RootAdjacent s L M) :
    RootAdjacent s (L.map f.toMonoidHom) (M.map f.toMonoidHom) := by
  obtain ⟨hne, x, hx, hxn, y, hy, hyn, hc, hp⟩ := h
  refine ⟨fun he => hne ((Subgroup.map_injective (f := f.toMonoidHom) f.injective) he),
    f x, ⟨x, hx, rfl⟩, ?_, f y, ⟨y, hy, rfl⟩, ?_, ?_, ?_⟩
  · intro he
    exact hxn (f.injective (he.trans f.map_one.symm))
  · intro he
    exact hyn (f.injective (he.trans f.map_one.symm))
  · change f x * f y = f y * f x
    simpa only [map_mul] using congrArg f hc.eq
  · simpa only [map_mul] using (automorphism_isLongRootElement_iff p h2 s f (x * y)).mpr hp

theorem rootAdjacent_map_iff (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryRootGroup K (s + 3)))
    (L M : Subgroup (elementaryRootGroup K (s + 3))) :
    RootAdjacent s (L.map f.toMonoidHom) (M.map f.toMonoidHom) ↔ RootAdjacent s L M := by
  constructor
  · intro h
    have hb := rootAdjacent_map p h2 s f.symm _ _ h
    have he : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact f.symm_apply_apply x
    rw [Subgroup.map_map, Subgroup.map_map, he, Subgroup.map_id, Subgroup.map_id] at hb
    exact hb
  · exact rootAdjacent_map p h2 s f L M

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBIntrinsicLongRoots

namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBUnipotent CFSGOrthogonalBIntrinsicLongRoots
variable {K : Type} [Field K] [Finite K]

private theorem rootAdjacent_labels_iff (h2 : (2 : K) ≠ 0) (s : ℕ)
    (P Q : Planes (K := K) s) :
    RootAdjacent s (label h2 s P) (label h2 s Q) ↔ PlaneAdjacent s P.val Q.val := by
  change RootAdjacent s (conjugateRootLine h2 s (representative s P))
    (conjugateRootLine h2 s (representative s Q)) ↔ _
  rw [representative_spec s P, representative_spec s Q]
  exact rootAdjacent_iff_planeAdjacent h2 s _ _

theorem action_preserves_adjacency (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryRootGroup K (s + 3)))
    (P Q : Planes (K := K) s) :
    PlaneAdjacent s (actionHom p h2 s f P).val (actionHom p h2 s f Q).val ↔
      PlaneAdjacent s P.val Q.val := by
  calc
    _ ↔ RootAdjacent s (label h2 s (actionHom p h2 s f P))
        (label h2 s (actionHom p h2 s f Q)) := (rootAdjacent_labels_iff h2 s _ _).symm
    _ ↔ RootAdjacent s ((label h2 s P).map f.toMonoidHom)
        ((label h2 s Q).map f.toMonoidHom) := by rw [label_action, label_action]
    _ ↔ RootAdjacent s (label h2 s P) (label h2 s Q) := rootAdjacent_map_iff p h2 s f _ _
    _ ↔ PlaneAdjacent s P.val Q.val := rootAdjacent_labels_iff h2 s P Q

def naturalLift (p : ℕ) [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) (s : ℕ)
    (f : MulAut (elementaryProjective K (s + 3))) : MulAut (elementaryRootGroup K (s + 3)) :=
  let e := oddProjectiveEquiv K p h2 (s + 2)
  e.trans (f.trans e.symm)

theorem projectiveAction_eq_natural (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s + 3)))
    (P : Planes (K := K) s) :
    projectiveActionHom p h2 s f P = actionHom p h2 s (naturalLift p h2 s f) P := by
  let e := oddProjectiveEquiv K p h2 (s + 2)
  let fE := naturalLift p h2 s f
  have heq : f.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp fE.toMonoidHom := by
    ext x
    change f (e x) = e (e.symm (f (e x)))
    exact (e.apply_symm_apply _).symm
  apply projectiveLabel_injective p h2 s
  rw [projectiveLabel_action]
  change ((label h2 s P).map e.toMonoidHom).map f.toMonoidHom =
    (label h2 s (actionHom p h2 s fE P)).map e.toMonoidHom
  rw [label_action, Subgroup.map_map, Subgroup.map_map, heq]

theorem projectiveAction_preserves_adjacency (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s + 3)))
    (P Q : Planes (K := K) s) :
    PlaneAdjacent s (projectiveActionHom p h2 s f P).val (projectiveActionHom p h2 s f Q).val ↔
      PlaneAdjacent s P.val Q.val := by
  rw [projectiveAction_eq_natural, projectiveAction_eq_natural]
  exact action_preserves_adjacency p h2 s (naturalLift p h2 s f) P Q

private theorem singularAction_transport (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s + 3)))
    (P : SingularPlanes (K := K) s) :
    singularPlaneEquiv h2 s (singularActionHom p h2 s f P) =
      projectiveActionHom p h2 s f (singularPlaneEquiv h2 s P) := by
  apply projectiveLabel_injective p h2 s
  change singularLabel h2 s (singularActionHom p h2 s f P) = _
  rw [singularLabel_action, projectiveLabel_action]
  rfl

theorem singularAction_preserves_adjacency (p : ℕ) [Fact p.Prime] [CharP K p]
    (h2 : (2 : K) ≠ 0) (s : ℕ) (f : MulAut (elementaryProjective K (s + 3)))
    (P Q : SingularPlanes (K := K) s) :
    PlaneAdjacent s (singularActionHom p h2 s f P).val (singularActionHom p h2 s f Q).val ↔
      PlaneAdjacent s P.val Q.val := by
  have hP := congrArg Subtype.val (singularAction_transport p h2 s f P)
  have hQ := congrArg Subtype.val (singularAction_transport p h2 s f Q)
  have he := projectiveAction_preserves_adjacency p h2 s f
    (singularPlaneEquiv h2 s P) (singularPlaneEquiv h2 s Q)
  rw [← hP, ← hQ] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPlaneFamilyAction
