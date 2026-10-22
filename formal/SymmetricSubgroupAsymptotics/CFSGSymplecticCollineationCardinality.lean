import SymmetricSubgroupAsymptotics.CFSGSymplecticCollineationSimilitudes
import SymmetricSubgroupAsymptotics.CFSGOrbitCoverCardinality

/-! Counting the actual orthogonality-preserving collineations charges
PGSp and the field stabilizer, rather than the whole PGL. The scalar
kernel has already been cancelled in the actual projective image. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticCollineationSimilitudes
open CFSGSymplecticSerreMatrices CFSGSymplecticPolarity
open CFSGProjectiveFrameCoordinates CFSGProjectiveFieldAction
variable {K : Type} [Field K] [Finite K]

def coordinateFrame (n : ℕ) (b : Index n) : (Index n ⊕ Unit) → Points K n :=
  Sum.elim (basisPoint (F := K)) (fun _ => sumPoint b)

def frameForget (n : ℕ) (b : Index n) :
    MulAction.stabilizer (orthogonalGroup (K := K) n) (coordinateFrame (K := K) n b) →
      frameStabilizer (F := K) b := fun h => ⟨h.val.val, by
  have hh : h.val • coordinateFrame (K := K) n b = coordinateFrame (K := K) n b := h.property
  apply (mem_frameStabilizer_iff b _).mpr
  exact ⟨fun i => congrFun hh (.inl i), congrFun hh (.inr ())⟩⟩

theorem frameForget_injective (n : ℕ) (b : Index n) :
    Function.Injective (frameForget (K := K) n b) := by
  intro x y h
  have hc : x.val.val = y.val.val := congrArg (fun z : frameStabilizer (F := K) b => z.val) h
  exact Subtype.ext (Subtype.ext hc)

theorem orthogonalGroup_card_le (n : ℕ) (hn : 0 < n) (b i j : Index n)
    (hbi : b ≠ i) (hbj : b ≠ j) (hij : i ≠ j) :
    Nat.card (orthogonalGroup (K := K) n) ≤
      Nat.card (elementaryRootGroup K n) * Nat.card (K ≃+* K) := by
  let R := (CFSGSymplecticSimilitudeGroup.pointHom (K := K) n).range
  letI : MulAction R (Points K n) := MulAction.compHom _ R.subtype
  have hcover : ∀ f : orthogonalGroup (K := K) n,
      ∃ g : R, f • coordinateFrame (K := K) n b = g • coordinateFrame (K := K) n b := by
    intro f
    obtain ⟨g, s, hs⟩ := exists_similitude_decomposition n hn f b i j hbi hbj hij
    refine ⟨⟨CFSGSymplecticSimilitudeGroup.pointHom n g, ⟨g, rfl⟩⟩, ?_⟩
    funext x
    cases x with
    | inl k =>
      change f.val.val (basisPoint k) = CFSGSymplecticSimilitudeGroup.pointHom n g (basisPoint k)
      rw [hs]
      exact congrArg (CFSGSymplecticSimilitudeGroup.pointHom n g) (collineation_basisPoint s k)
    | inr u =>
      cases u
      change f.val.val (sumPoint b) = CFSGSymplecticSimilitudeGroup.pointHom n g (sumPoint b)
      rw [hs]
      exact congrArg (CFSGSymplecticSimilitudeGroup.pointHom n g) (collineation_sumPoint s b)
  have hc := CFSGOrbitCoverCardinality.card_le_cover_mul_stabilizer
    (G := R) (H := orthogonalGroup (K := K) n) (coordinateFrame (K := K) n b) hcover
  have hs : Nat.card (MulAction.stabilizer (orthogonalGroup (K := K) n) (coordinateFrame (K := K) n b)) ≤
      Nat.card (K ≃+* K) :=
    (Nat.card_le_card_of_injective _ (frameForget_injective n b)).trans
      (frameStabilizer_card_le_of_three_coordinates b i j hbi hbj hij)
  have hR : Nat.card R = Nat.card (elementaryRootGroup K n) :=
    CFSGSymplecticSimilitudeGroup.projectiveSimilitudes_card n hn
  rw [hR] at hc
  exact hc.trans (Nat.mul_le_mul_left _ hs)

end SymmetricSubgroupAsymptotics.CFSGSymplecticCollineationSimilitudes
