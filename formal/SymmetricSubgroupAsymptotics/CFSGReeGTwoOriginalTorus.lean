import SymmetricSubgroupAsymptotics.CFSGGTwoOriginalRankTwoTorus
import SymmetricSubgroupAsymptotics.CFSGReeGTwoFixedModelEquivalence
import Mathlib.Algebra.Group.Units.Equiv

/-! The actual original rank-two torus is stable under the prescribed
Ree involution. Its fixed part is parametrized faithfully by one field
unit. Neither an ordinary G2 simplicity hypothesis nor a torus-normalizer
identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalTorus
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration
open CFSGGTwoOriginalRankTwoTorus CFSGReeGTwoFieldParameters
open CFSGReeGTwoOriginalAutomorphism CFSGReeGTwoFixedModelEquivalence
local notation "A" => CartanMatrix.G₂

private theorem map_node {K : Type} [Field K]
    (f : Model A K →* Model A K) (sigma : K ≃+* K) (i j : Fin 2)
    (hf : ∀ neg t, f (modelRoot A K neg i t) = modelRoot A K neg j (sigma t))
    (t : Kˣ) :
    f (torusNode K i t) = torusNode K j (Units.mapEquiv sigma.toMulEquiv t) := by
  simp only [torusNode, weylParameter, map_mul, hf]
  simp [Units.mapEquiv, Units.map, map_neg]

def unitsAlpha (m : ℕ) : (Field m)ˣ ≃* (Field m)ˣ :=
  Units.mapEquiv (alphaEquiv m).toMulEquiv

@[simp] theorem unitsAlpha_val (m : ℕ) (t : (Field m)ˣ) :
    (unitsAlpha m t : Field m) = alpha m (t : Field m) := rfl

@[simp] theorem unitsAlpha_symm_val (m : ℕ) (t : (Field m)ˣ) :
    ((unitsAlpha m).symm t : Field m) = beta m (t : Field m) := rfl

private theorem ree_short_root (m : ℕ) (neg : Bool) (t : Field m) :
    reeAutomorphism m (modelRoot A (Field m) neg 0 t) =
      modelRoot A (Field m) neg 1 (alphaEquiv m t) := by
  have h := reeAutomorphism_root m neg (0 : Fin 2) t
  change reeAutomorphism m (modelRoot A (Field m) neg 0 t) =
    modelRoot A (Field m) neg 1 (t ^ (3 ^ (m + 1))) at h
  exact h

private theorem ree_long_root (m : ℕ) (neg : Bool) (t : Field m) :
    reeAutomorphism m (modelRoot A (Field m) neg 1 t) =
      modelRoot A (Field m) neg 0 ((alphaEquiv m).symm t) := by
  have h := reeAutomorphism_root m neg (1 : Fin 2) t
  change reeAutomorphism m (modelRoot A (Field m) neg 1 t) =
    modelRoot A (Field m) neg 0 (t ^ (3 ^ m)) at h
  exact h

theorem ree_short_torus (m : ℕ) (t : (Field m)ˣ) :
    reeAutomorphism m (torusNode (Field m) 0 t) =
      torusNode (Field m) 1 (unitsAlpha m t) :=
  map_node (reeAutomorphism m).toMonoidHom (alphaEquiv m) 0 1 (ree_short_root m) t

theorem ree_long_torus (m : ℕ) (t : (Field m)ˣ) :
    reeAutomorphism m (torusNode (Field m) 1 t) =
      torusNode (Field m) 0 ((unitsAlpha m).symm t) :=
  map_node (reeAutomorphism m).toMonoidHom (alphaEquiv m).symm 1 0 (ree_long_root m) t

theorem ree_torusPair (m : ℕ) (t : (Field m)ˣ × (Field m)ˣ) :
    reeAutomorphism m (torusPair (Field m) t) =
      torusPair (Field m) ((unitsAlpha m).symm t.2, unitsAlpha m t.1) := by
  simp only [torusPair, map_mul, ree_short_torus, ree_long_torus]
  exact (nodes_commute (Field m) ((unitsAlpha m).symm t.2) (unitsAlpha m t.1)).eq.symm

theorem torusPair_fixed_iff (m : ℕ) (t : (Field m)ˣ × (Field m)ˣ) :
    reeAutomorphism m (torusPair (Field m) t) = torusPair (Field m) t ↔
      t.2 = unitsAlpha m t.1 := by
  rw [ree_torusPair]
  constructor
  · intro h
    exact (congrArg Prod.snd (torusPair_injective (Field m) h)).symm
  · intro h
    apply congrArg (torusPair (Field m))
    apply Prod.ext
    · rw [h, (unitsAlpha m).symm_apply_apply]
    · exact h.symm

def fixedParameterHom (m : ℕ) : (Field m)ˣ →* (Field m)ˣ × (Field m)ˣ :=
  (MonoidHom.id _).prod (unitsAlpha m).toMonoidHom

def fixedTorusHom (m : ℕ) : (Field m)ˣ →* originalModelFixed m :=
  ((torusHom (Field m)).comp (fixedParameterHom m)).codRestrict (originalModelFixed m) (by
    intro t
    change reeAutomorphism m (torusHom (Field m) (t, unitsAlpha m t)) =
      torusHom (Field m) (t, unitsAlpha m t)
    rw [torusHom_apply]
    exact (torusPair_fixed_iff m (t, unitsAlpha m t)).mpr rfl)

theorem fixedTorusHom_val (m : ℕ) (t : (Field m)ˣ) :
    (fixedTorusHom m t).val = torusPair (Field m) (t, unitsAlpha m t) :=
  torusHom_apply (Field m) _

theorem fixedTorusHom_injective (m : ℕ) : Function.Injective (fixedTorusHom m) := by
  intro a b h
  have he := congrArg (fun g : originalModelFixed m => g.val) h
  dsimp only at he
  rw [fixedTorusHom_val, fixedTorusHom_val] at he
  exact congrArg Prod.fst (torusPair_injective (Field m) he)

theorem fixedTorus_range_card (m : ℕ) :
    Nat.card (fixedTorusHom m).range = Nat.card ((Field m)ˣ) :=
  (Nat.card_congr (Equiv.ofInjective (fixedTorusHom m) (fixedTorusHom_injective m))).symm

theorem fixedTorus_card (m : ℕ) :
    Nat.card (fixedTorusHom m).range = 3 ^ (2 * m + 1) - 1 := by
  rw [fixedTorus_range_card, Nat.card_units, field_card]

theorem fixed_torus_range_iff (m : ℕ) (g : originalModelFixed m) :
    g.val ∈ (torusHom (Field m)).range ↔ g ∈ (fixedTorusHom m).range := by
  constructor
  · rintro ⟨t, ht⟩
    rcases t with ⟨a, b⟩
    have he : torusPair (Field m) (a, b) = g.val :=
      (torusHom_apply (Field m) (a, b)).symm.trans ht
    have hf : reeAutomorphism m (torusPair (Field m) (a, b)) =
        torusPair (Field m) (a, b) := by
      rw [he]
      exact g.property
    have hp : b = unitsAlpha m a := (torusPair_fixed_iff m (a, b)).mp hf
    subst b
    refine ⟨a, Subtype.ext ?_⟩
    exact (fixedTorusHom_val m a).trans he
  · rintro ⟨t, rfl⟩
    exact ⟨(t, unitsAlpha m t),
      (torusHom_apply (Field m) (t, unitsAlpha m t)).trans
        (fixedTorusHom_val m t).symm⟩

end SymmetricSubgroupAsymptotics.CFSGReeGTwoOriginalTorus
