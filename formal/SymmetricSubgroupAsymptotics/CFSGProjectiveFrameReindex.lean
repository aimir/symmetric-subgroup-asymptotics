import SymmetricSubgroupAsymptotics.CFSGProjectiveLinearEquivalence
import SymmetricSubgroupAsymptotics.CFSGProjectiveFrameFieldAutomorphism

/-! Literal coordinate relabelling transports the original projective
frame stabilizer. The field bound therefore applies in any coordinate type
with three distinct coordinates. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
variable {F n m : Type*} [Field F] [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def transportCollineation (L : (n→F)≃ₗ[F](m→F))
    (f : collineationGroup (F:=F) (n:=n)) : collineationGroup (F:=F) (n:=m) :=
  let e := linearPointEquiv L
  ⟨e.symm.trans (f.val.trans e),by
    intro p q r
    change OnLine (e (f.val (e.symm p))) (e (f.val (e.symm q))) (e (f.val (e.symm r)))↔OnLine p q r
    apply (onLine_linearPointEquiv L _ _ _).trans
    apply (f.property _ _ _).trans
    have hh := (onLine_linearPointEquiv L (e.symm p) (e.symm q) (e.symm r)).symm
    simpa only [e,Equiv.apply_symm_apply] using hh⟩

theorem transportCollineation_injective (L : (n→F)≃ₗ[F](m→F)) :
    Function.Injective (transportCollineation L) := by
  intro f g he
  apply Subtype.ext
  apply Equiv.ext
  intro p
  have hh := congrArg (fun h : collineationGroup (F:=F) (n:=m) => h.val (linearPointEquiv L p)) he
  apply (linearPointEquiv L).injective
  simpa only [transportCollineation,Equiv.trans_apply,Equiv.symm_apply_apply] using hh

def coordinateLinearEquiv (e : n≃m) : (n→F)≃ₗ[F](m→F) :=
  LinearEquiv.piCongrLeft' F (fun _ : n => F) e

theorem coordinateLinearEquiv_apply (e : n≃m) (v : n→F) (j : m) :
    coordinateLinearEquiv (F:=F) e v j=v (e.symm j) := rfl

theorem coordinateLinearEquiv_single (e : n≃m) (i : n) :
    coordinateLinearEquiv (F:=F) e (Pi.single i 1)=Pi.single (e i) 1 := by
  funext j
  rw [coordinateLinearEquiv_apply]
  by_cases hji : j=e i
  · subst j
    simp only [Pi.single_eq_same]
    change (Pi.single i 1 : n→F) (e.symm (e i))=1
    calc
      (Pi.single i (1:F) : n→F) (e.symm (e i))=(Pi.single i (1:F) : n→F) i :=
        congrArg (Pi.single i (1:F) : n→F) (e.symm_apply_apply i)
      _=1 := by simp [Pi.single_apply]
  · have hs : e.symm j≠i := by
      intro he
      exact hji ((e.apply_symm_apply j).symm.trans (congrArg e he))
    simp only [Pi.single_apply,hs,hji,↓reduceIte]

theorem coordinatePoint_basis (e : n≃m) (i : n) :
    linearPointEquiv (coordinateLinearEquiv (F:=F) e) (basisPoint (F:=F) i)=basisPoint (F:=F) (e i) := by
  unfold basisPoint
  rw [linearPointEquiv_mk]
  simp only [coordinateLinearEquiv_single]

theorem coordinatePoint_sum (e : n≃m) (b : n) :
    linearPointEquiv (coordinateLinearEquiv (F:=F) e) (sumPoint (F:=F) b)=sumPoint (F:=F) (e b) := by
  unfold sumPoint
  rw [linearPointEquiv_mk]
  rfl

def reindexFrameMap (e : n≃m) (b : n) :
    frameStabilizer (F:=F) b→frameStabilizer (F:=F) (e b) := fun f =>
  ⟨transportCollineation (coordinateLinearEquiv e) f.val,by
    have hf := (mem_frameStabilizer_iff b f.val).mp f.property
    apply (mem_frameStabilizer_iff _ _).mpr
    constructor
    · intro j
      have hp := coordinatePoint_basis (F:=F) e (e.symm j)
      simp only [Equiv.apply_symm_apply] at hp
      change linearPointEquiv (coordinateLinearEquiv e)
        (f.val.val ((linearPointEquiv (coordinateLinearEquiv e)).symm (basisPoint (F:=F) j)))=
          basisPoint (F:=F) j
      rw [←hp,Equiv.symm_apply_apply]
      exact congrArg (linearPointEquiv (coordinateLinearEquiv e)) (hf.1 (e.symm j))
    · have hp := coordinatePoint_sum (F:=F) e b
      change linearPointEquiv (coordinateLinearEquiv e)
        (f.val.val ((linearPointEquiv (coordinateLinearEquiv e)).symm (sumPoint (F:=F) (e b))))=
          sumPoint (F:=F) (e b)
      rw [←hp,Equiv.symm_apply_apply]
      exact congrArg (linearPointEquiv (coordinateLinearEquiv e)) hf.2⟩

theorem reindexFrameMap_injective (e : n≃m) (b : n) :
    Function.Injective (reindexFrameMap (F:=F) e b) := by
  intro f g he
  apply Subtype.ext
  apply transportCollineation_injective (coordinateLinearEquiv (F:=F) e)
  exact congrArg Subtype.val he

private def splitBase (b : n) : n≃Unit⊕{i : n // i≠b} where
  toFun i := if h : i=b then Sum.inl () else Sum.inr ⟨i,h⟩
  invFun := Sum.elim (fun _ => b) Subtype.val
  left_inv i := by
    by_cases h : i=b
    · simp only [h,↓reduceDIte,Sum.elim_inl]
    · simp only [h,↓reduceDIte,Sum.elim_inr]
  right_inv i := by
    rcases i with u | i
    · cases u
      simp only [Sum.elim_inl,↓reduceDIte]
    · simp only [Sum.elim_inr,i.property,↓reduceDIte]

theorem frameStabilizer_card_le_of_three_coordinates [Finite F]
    (b i j : n) (hbi : b≠i) (hbj : b≠j) (hij : i≠j) :
    Nat.card (frameStabilizer (F:=F) b)≤Nat.card (F≃+*F) := by
  let e := splitBase b
  let i' : {k : n // k≠b} := ⟨i,Ne.symm hbi⟩
  let j' : {k : n // k≠b} := ⟨j,Ne.symm hbj⟩
  have hij' : i'≠j' := fun he => hij (congrArg Subtype.val he)
  exact (Nat.card_le_card_of_injective (reindexFrameMap (F:=F) e b)
    (reindexFrameMap_injective e b)).trans (frameStabilizer_card_le (e b) i' j' hij')

end SymmetricSubgroupAsymptotics.CFSGProjectiveFrameCoordinates
