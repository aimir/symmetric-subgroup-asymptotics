import SymmetricSubgroupAsymptotics.MarkedC4NilpotentLabelledActions
import SymmetricSubgroupAsymptotics.MarkedC4NilpotentFiberOrbitBounds
import SymmetricSubgroupAsymptotics.MarkedC4EmbeddedPermutationOrbit

/-! The SAME original orbit cutoff passes through actual fiber compression
and finite-label images. No cutoff property of a replacement group is assumed. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.NilpotentCompressedCutoff
open NilpotentSylowFactors NilpotentPermutationGrid NilpotentCompressedImages

private theorem range_comp {A B D : Type} [Group A] [Group B] [Group D]
    (f : B →* D) (p : A →* B) (hp : Function.Surjective p) :
    (f.comp p).range=f.range := by
  ext z
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨p a,rfl⟩
  · rintro ⟨b,rfl⟩
    obtain ⟨a,rfl⟩ := hp b
    exact ⟨a,rfl⟩

variable {b C : ℕ} (K : Subgroup (PermutationGroup b)) [Group.IsNilpotent K]
  (hC : 1<C) (hK : ∀ x : Fin b,Nat.card (MulAction.orbit K x)<C)
local instance : Fintype (OrbitIndex K (Fin b)) := Fintype.ofFinite _
local instance (ω : OrbitIndex K (Fin b)) : Fintype (BinaryFiber K (Fin b) ω) := Fintype.ofFinite _
local instance (ω : OrbitIndex K (Fin b)) : Fintype (OddFiber K (Fin b) ω) := Fintype.ofFinite _
local instance : Fintype (PhysicalGridLabels.Active (BinaryFiber K (Fin b))) :=
  ActiveCoordinateLabels.instFintypeActive (BinaryFiber K (Fin b))
local instance : Fintype (PhysicalGridLabels.Active (OddFiber K (Fin b))) :=
  ActiveCoordinateLabels.instFintypeActive (OddFiber K (Fin b))

include hC hK in
theorem binary_cutoff : ∀ x : Fin (b+1),
    Nat.card (MulAction.orbit (NilpotentLabelledActions.binary K).range x)<C := by
  have hb : Fintype.card (PhysicalGridLabels.Active (BinaryFiber K (Fin b)))≤b := by
    have h := physical_budget K (Fin b)
    have ha := (Nat.le_add_right (Nat.card (BinarySupport K (Fin b)))
      (Nat.card (OddSupport K (Fin b)))).trans h
    change Nat.card (PhysicalGridLabels.Active (BinaryFiber K (Fin b))) ≤ Nat.card (Fin b) at ha
    simpa only [Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_fin] using ha
  let p : K →* Binary K := (MonoidHom.fst _ _).comp (equiv K).toMonoidHom
  have hp : Function.Surjective p := by
    intro g
    refine ⟨(equiv K).symm (g,1),?_⟩
    change ((equiv K) ((equiv K).symm (g,1))).1=g
    rw [(equiv K).apply_symm_apply]
  have hr : (NilpotentLabelledActions.binary K).range=
      (ActiveCoordinateLabels.action (G := Binary K) (BinaryFiber K (Fin b)) hb).range :=
    range_comp _ p hp
  rw [hr]
  apply EmbeddedPermutationOrbit.cutoff
    (ActiveCoordinateLabels.embedding (BinaryFiber K (Fin b)) hb) hC
  apply ActiveFiberOrbitBounds.cutoff
  exact (NilpotentFiberOrbitBounds.fiber_cutoff K (Fin b) hK).1

include hC hK in
theorem odd_cutoff : ∀ x : Fin (b+1),
    Nat.card (MulAction.orbit (NilpotentLabelledActions.odd K).range x)<C := by
  have hd : Fintype.card (PhysicalGridLabels.Active (OddFiber K (Fin b)))≤b := by
    have h := physical_budget K (Fin b)
    have ha := (Nat.le_add_left (Nat.card (OddSupport K (Fin b)))
      (Nat.card (BinarySupport K (Fin b)))).trans h
    change Nat.card (PhysicalGridLabels.Active (OddFiber K (Fin b))) ≤ Nat.card (Fin b) at ha
    simpa only [Nat.card_fin,Nat.card_eq_fintype_card,Fintype.card_fin] using ha
  let p : K →* OddFactor K := (MonoidHom.snd _ _).comp (equiv K).toMonoidHom
  have hp : Function.Surjective p := by
    intro g
    refine ⟨(equiv K).symm (1,g),?_⟩
    change ((equiv K) ((equiv K).symm (1,g))).2=g
    rw [(equiv K).apply_symm_apply]
  have hr : (NilpotentLabelledActions.odd K).range=
      (ActiveCoordinateLabels.action (G := OddFactor K) (OddFiber K (Fin b)) hd).range :=
    range_comp _ p hp
  rw [hr]
  apply EmbeddedPermutationOrbit.cutoff
    (ActiveCoordinateLabels.embedding (OddFiber K (Fin b)) hd) hC
  apply ActiveFiberOrbitBounds.cutoff
  exact (NilpotentFiberOrbitBounds.fiber_cutoff K (Fin b) hK).2
end SymmetricSubgroupAsymptotics.MarkedC4.NilpotentCompressedCutoff
