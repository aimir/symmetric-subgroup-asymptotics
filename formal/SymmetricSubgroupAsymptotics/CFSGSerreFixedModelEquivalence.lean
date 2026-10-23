import SymmetricSubgroupAsymptotics.CFSGSerreModelHomGraph
import SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv
import Mathlib.GroupTheory.Commutator.Basic

/-! Literal fixed groups, derived groups and central quotients can all be
transported inside the original Model once its prescribed graph is realized.
The realizing homomorphism need not extend to the ambient linear group.
No simplicity or fixed-quotient lifting hypothesis occurs here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreFixedModelEquivalence
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreModelHomGraph

variable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (K : Type) [Field K]

def fixedModel (phi : Model A K →* Model A K) : Subgroup (Model A K) where
  carrier := {g | phi g = g}
  one_mem' := map_one phi
  mul_mem' := by intro a b ha hb; exact (map_mul phi a b).trans (congrArg₂ (· * ·) ha hb)
  inv_mem' := by intro a ha; exact (map_inv phi a).trans (congrArg Inv.inv ha)

variable (perm : Fin n → Fin n) (exponent : Fin n → ℕ)
    (phi : Model A K →* Model A K)
    (hphi : ∀ neg i t, phi (modelRoot A K neg i t) =
      modelRoot A K neg (perm i) (t ^ exponent i))

def fixedModelEquiv : fixedSubgroup A K perm exponent ≃* fixedModel A K phi where
  toFun g := ⟨⟨g.val, g.property.1⟩,
    (mem_fixedSubgroup_model_iff A K perm exponent phi hphi ⟨g.val, g.property.1⟩).mp
      g.property⟩
  invFun g := ⟨g.val.val,
    (mem_fixedSubgroup_model_iff A K perm exponent phi hphi g.val).mpr g.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)
  map_mul' _ _ := rfl

@[simp] theorem fixedModelEquiv_val (g : fixedSubgroup A K perm exponent) :
    (fixedModelEquiv A K perm exponent phi hphi g).val.val = g.val := rfl

def derivedEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    commutator G ≃* commutator H :=
  (e.subgroupMap (commutator G)).trans (MulEquiv.subgroupCongr (by
    simp only [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (e : G →* H) e.surjective]))

abbrev DerivedCentralQuotient (G : Type*) [Group G] :=
  let D := ↥(commutator G)
  D ⧸ Subgroup.center D

def twistedFixedModelEquiv :
    Twisted A K perm exponent ≃* DerivedCentralQuotient (fixedModel A K phi) :=
  CFSGCenterQuotientEquiv.equiv
    (derivedEquiv (fixedModelEquiv A K perm exponent phi hphi))

end SymmetricSubgroupAsymptotics.CFSGSerreFixedModelEquivalence
