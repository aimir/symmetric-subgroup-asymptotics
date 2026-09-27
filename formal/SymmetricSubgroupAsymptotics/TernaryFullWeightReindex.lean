import SymmetricSubgroupAsymptotics.DiagonalFullSubmoduleWeights

/-! Reindex original coordinate sets without changing the full-subspace
weight. The canonical factor depends only on the number of coordinates;
this reindexing does not change the actual source group or identify its
different sign isotypes. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.TernaryFullWeightReindex

open DiagonalInvariantSubmodules DiagonalFullSubmoduleEquiv DiagonalFullSubmoduleWeights

variable {k I J : Type*} [Field k]

def coordinateEquiv (e : I ≃ J) : (I → k) ≃ₗ[k] (J → k) where
  toFun v j := v (e.symm j)
  invFun w i := w (e i)
  left_inv v := by funext i; simp
  right_inv w := by funext j; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem full_map_iff (e : I ≃ J) (K : Submodule k (I → k)) :
    FullCoordinates K ↔ FullCoordinates (K.map (coordinateEquiv (k := k) e).toLinearMap) := by
  constructor
  · intro h j c
    obtain ⟨v,hv⟩ := h (e.symm j) c
    exact ⟨⟨coordinateEquiv e v.1,⟨v.1,v.2,rfl⟩⟩,hv⟩
  · intro h i c
    obtain ⟨w,hw⟩ := h (e i) c
    obtain ⟨v,hv,he⟩ := w.2
    refine ⟨⟨v,hv⟩,?_⟩
    have hx := congrFun he (e i)
    change v (e.symm (e i))=w.1 (e i) at hx
    rw [e.symm_apply_apply] at hx
    exact hx.trans hw

def fullEquiv (e : I ≃ J) :
    FullSubmodule (k := k) I ≃ FullSubmodule (k := k) J :=
  (Submodule.orderIsoMapComap (coordinateEquiv (k := k) e)).toEquiv.subtypeEquiv
    (fun K => full_map_iff e K)

@[simp] theorem fullEquiv_val (e : I ≃ J) (K : FullSubmodule (k := k) I) :
    (fullEquiv e K).1=K.1.map (coordinateEquiv (k := k) e).toLinearMap := rfl

theorem fullEquiv_finrank (e : I ≃ J) (K : FullSubmodule (k := k) I) :
    Module.finrank k (fullEquiv e K).1=Module.finrank k K.1 :=
  ((coordinateEquiv (k := k) e).submoduleMap K.1).finrank_eq.symm

section Ternary

variable [Fintype I] [Fintype J]

local instance fullSubmoduleFinite (T : Type*) [Fintype T] :
    Finite (FullSubmodule (k := ZMod 3) T) :=
  Finite.of_injective (fun K : FullSubmodule (k := ZMod 3) T =>
    (K.1 : Set (T → ZMod 3)))
    (fun _ _ h => Subtype.ext (SetLike.coe_injective h))

attribute [local instance] Fintype.ofFinite

/-- The literal full-coordinate subspace weight is invariant under an
actual reindexing of its coordinate set. -/
theorem weight_eq (e : I ≃ J) : ternaryFullWeight I=ternaryFullWeight J := by
  unfold ternaryFullWeight
  apply Fintype.sum_equiv (fullEquiv (k := ZMod 3) e)
  intro K
  rw [fullEquiv_finrank,Fintype.card_congr e]

end Ternary

/-- The canonical one-isotype factor used in the manuscript. -/
def ternaryFullFactor (a : ℕ) : ℕ := ternaryFullWeight (Fin a)

theorem weight_eq_factor (I : Type*) [Fintype I] :
    ternaryFullWeight I=ternaryFullFactor (Fintype.card I) :=
  weight_eq (Fintype.equivFin I)

end SymmetricSubgroupAsymptotics.TernaryFullWeightReindex

end

