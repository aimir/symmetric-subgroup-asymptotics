import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEquivalence
import Mathlib.LinearAlgebra.Pi

/-! Coordinatewise field automorphisms give literal projective
collineations fixing the standard frame. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction
open CFSGProjectiveFrameCoordinates
variable {F n : Type*} [Field F]

local instance (s : F ≃+* F) : RingHomInvPair s.toRingHom s.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv s
local instance (s : F ≃+* F) : RingHomInvPair s.symm.toRingHom s.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm s

def coordinateEquiv (s : F ≃+* F) : (n → F) ≃ₛₗ[s.toRingHom] (n → F) where
  toFun v := s ∘ v
  invFun v := s.symm ∘ v
  left_inv v := by funext i; exact s.symm_apply_apply (v i)
  right_inv v := by funext i; exact s.apply_symm_apply (v i)
  map_add' v w := by funext i; exact s.map_add (v i) (w i)
  map_smul' a v := by funext i; exact s.map_mul a (v i)

def pointEquiv (s : F ≃+* F) : Equiv.Perm (Points (F := F) (n := n)) where
  toFun := Projectivization.map (coordinateEquiv s).toLinearMap (coordinateEquiv s).injective
  invFun := Projectivization.map (coordinateEquiv s.symm).toLinearMap
    (coordinateEquiv s.symm).injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      change Projectivization.mk F (s.symm ∘ (s ∘ v)) _ = Projectivization.mk F v hv
      congr 1
      funext i
      exact s.symm_apply_apply (v i)
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv =>
      change Projectivization.mk F (s ∘ (s.symm ∘ v)) _ = Projectivization.mk F v hv
      congr 1
      funext i
      exact s.apply_symm_apply (v i)

theorem pointEquiv_mk (s : F ≃+* F) (v : n → F) (hv : v ≠ 0) :
    pointEquiv s (Projectivization.mk F v hv) = Projectivization.mk F
      (s ∘ v) (by
        intro hz
        apply hv
        funext i
        apply s.injective
        simpa only [Function.comp_apply, Pi.zero_apply, map_zero] using congrFun hz i) := rfl

theorem pointEquiv_submodule (s : F ≃+* F) (p : Points (F := F) (n := n)) :
    (pointEquiv s p).submodule = p.submodule.map (coordinateEquiv s).toLinearMap := by
  induction p using Projectivization.ind with
  | h v hv =>
    change F ∙ (s ∘ v) = (F ∙ v).map (coordinateEquiv s).toLinearMap
    rw [Submodule.map_span, Set.image_singleton]
    rfl

theorem onLine_pointEquiv (s : F ≃+* F) (p q r : Points (F := F) (n := n)) :
    OnLine (pointEquiv s p) (pointEquiv s q) (pointEquiv s r) ↔ OnLine p q r := by
  unfold OnLine
  rw [pointEquiv_submodule, pointEquiv_submodule, pointEquiv_submodule,
    ← Submodule.map_sup]
  exact Submodule.map_le_map_iff_of_injective (coordinateEquiv s).injective _ _

variable [Fintype n] [DecidableEq n]

def collineation (s : F ≃+* F) : collineationGroup (F := F) (n := n) :=
  ⟨pointEquiv s, onLine_pointEquiv s⟩

theorem collineation_basisPoint (s : F ≃+* F) (i : n) :
    (collineation s).val (basisPoint (F := F) i) = basisPoint i := by
  unfold basisPoint
  rw [show (collineation s).val = pointEquiv (n := n) s from rfl, pointEquiv_mk]
  congr 1
  funext j
  by_cases h : j = i <;> simp [Pi.single_apply, h, Function.comp_apply]

theorem collineation_sumPoint (s : F ≃+* F) (b : n) :
    (collineation s).val (sumPoint (F := F) b) = sumPoint b := by
  unfold sumPoint
  rw [show (collineation s).val = pointEquiv (n := n) s from rfl, pointEquiv_mk]
  congr 1
  funext j
  simp only [Function.comp_apply, map_one]

def frameMap (b : n) (s : F ≃+* F) : frameStabilizer (F := F) b :=
  ⟨collineation s, (mem_frameStabilizer_iff b _).mpr
    ⟨collineation_basisPoint s, collineation_sumPoint s b⟩⟩

end SymmetricSubgroupAsymptotics.CFSGProjectiveFieldAction
