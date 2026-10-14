import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel
import SymmetricSubgroupAsymptotics.PermutationOrbitCoverGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-!
# The literal four ternary blocks of row 131

The two original permutations are a translation on one three-point block
and a regular four-cycle on the blocks. The displayed point chart binds
them to `F₃⁴ ⋊ C₄`. Four conjugates of the local translation generate the
whole translation module; this is proved by coordinate decomposition,
without enumerating the generated permutation group.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow131AffineModel

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open SemidirectProduct

abbrev Block := Multiplicative (ZMod 4)
abbrev Vector := Block → ZMod 3
abbrev Translation := Multiplicative Vector
abbrev Points := Block × ZMod 3
abbrev Top := Row131Top

def linearAction : Block →* (Vector ≃ₗ[ZMod 3] Vector) where
  toFun c :=
    { toFun := fun v i ↦ v (c⁻¹ * i)
      invFun := fun v i ↦ v (c * i)
      left_inv := by intro v; funext i; simp
      right_inv := by intro v; funext i; simp
      map_add' := by intro v w; rfl
      map_smul' := by intro a v; rfl }
  map_one' := by
    apply LinearEquiv.ext
    intro v
    funext i
    simp
  map_mul' := by
    intro c d
    apply LinearEquiv.ext
    intro v
    funext i
    simp [mul_inv_rev, mul_assoc]

theorem linearAction_injective : Function.Injective linearAction := by
  intro c d h
  have hdelta := congrArg (fun f : Vector ≃ₗ[ZMod 3] Vector ↦
    f (Pi.single (1 : Block) (1 : ZMod 3))) h
  change permutationFunctionRepresentation (ZMod 3) Block Block c (Pi.single 1 1) =
    permutationFunctionRepresentation (ZMod 3) Block Block d (Pi.single 1 1) at hdelta
  rw [permutationFunctionRepresentation_single,
    permutationFunctionRepresentation_single] at hdelta
  have hdelta' : (Pi.single c (1 : ZMod 3) : Vector) = Pi.single d 1 := by
    simpa only [smul_eq_mul, mul_one] using hdelta
  by_contra hne
  have h := congrFun hdelta' c
  simpa [Pi.single_apply, hne, Ne.symm hne] using h

def linearGroup : Subgroup (AffineModel.GLV 3 4) := linearAction.range

def complementEquiv : Block ≃* linearGroup :=
  MonoidHom.ofInjective linearAction_injective

instance linearGroup_isCyclic : IsCyclic linearGroup :=
  isCyclic_of_surjective complementEquiv.toMonoidHom complementEquiv.surjective

theorem linearGroup_card : Nat.card linearGroup = 4 := by
  rw [← Nat.card_congr complementEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

def rotation : Block →* MulAut Translation where
  toFun c := (linearAction c).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd
      (LinearEquiv.congr_fun linearAction.map_one v.toAdd)
  map_mul' c d := by
    apply MulEquiv.ext
    intro v
    exact congrArg Multiplicative.ofAdd
      (LinearEquiv.congr_fun (linearAction.map_mul c d) v.toAdd)

abbrev Model := Translation ⋊[rotation] Block

instance : Finite Model := Finite.of_equiv _ SemidirectProduct.equivProd.symm

def affineEquiv : Model ≃* AffineModel.Aff linearGroup :=
  SemidirectProduct.congr (MulEquiv.refl Translation) complementEquiv
    (by intro c; apply MulEquiv.ext; intro v; rfl)

def translations : Translation →* Equiv.Perm Points where
  toFun v :=
    { toFun := fun p ↦ (p.1, v.toAdd p.1 + p.2)
      invFun := fun p ↦ (p.1, -v.toAdd p.1 + p.2)
      left_inv := by intro p; apply Prod.ext <;> simp
      right_inv := by intro p; apply Prod.ext <;> simp }
  map_one' := by apply Equiv.ext; intro p; apply Prod.ext <;> simp
  map_mul' := by
    intro v w
    apply Equiv.ext
    intro p
    apply Prod.ext
    · rfl
    · change (v.toAdd p.1 + w.toAdd p.1) + p.2 =
        v.toAdd p.1 + (w.toAdd p.1 + p.2)
      exact add_assoc _ _ _

def blockShifts : Block →* Equiv.Perm Points where
  toFun c :=
    { toFun := fun p ↦ (c * p.1, p.2)
      invFun := fun p ↦ (c⁻¹ * p.1, p.2)
      left_inv := by intro p; apply Prod.ext <;> simp
      right_inv := by intro p; apply Prod.ext <;> simp }
  map_one' := by apply Equiv.ext; intro p; apply Prod.ext <;> simp
  map_mul' := by
    intro c d
    apply Equiv.ext
    intro p
    apply Prod.ext
    · exact mul_assoc c d p.1
    · rfl

def modelAction : Model →* Equiv.Perm Points :=
  SemidirectProduct.lift translations blockShifts (by
    intro c
    apply MonoidHom.ext
    intro v
    apply Equiv.ext
    intro p
    apply Prod.ext <;>
      simp [translations, blockShifts, rotation, linearAction, mul_assoc])

theorem modelAction_apply (g : Model) (p : Points) :
    modelAction g p = (g.right * p.1, g.left.toAdd (g.right * p.1) + p.2) := rfl

theorem modelAction_injective : Function.Injective modelAction := by
  apply (injective_iff_map_eq_one modelAction).2
  intro g hg
  have hright := congrArg Prod.fst (Equiv.congr_fun hg (1, 0))
  change g.right * 1 = 1 at hright
  rw [mul_one] at hright
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    have h := congrArg Prod.snd (Equiv.congr_fun hg (i, 0))
    change g.left.toAdd (g.right * i) + 0 = 0 at h
    simpa only [hright, one_mul, add_zero] using h
  · exact hright

/-- The origins are transported around the actual four-cycle, so its
action has no hidden shifts inside a ternary block. -/
def pointEquiv : Fin 12 ≃ Points where
  toFun := ![(Multiplicative.ofAdd 3, 0), (Multiplicative.ofAdd 2, 1),
    (Multiplicative.ofAdd 1, 2), (Multiplicative.ofAdd 0, 0),
    (Multiplicative.ofAdd 3, 1), (Multiplicative.ofAdd 2, 2),
    (Multiplicative.ofAdd 1, 0), (Multiplicative.ofAdd 0, 1),
    (Multiplicative.ofAdd 3, 2), (Multiplicative.ofAdd 2, 0),
    (Multiplicative.ofAdd 1, 1), (Multiplicative.ofAdd 0, 2)]
  invFun p := (#[3, 7, 11, 6, 10, 2, 9, 1, 5, 0, 4, 8] : Array (Fin 12))[
    3 * p.1.toAdd.val + p.2.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def literalAction : Model →* Equiv.Perm (Fin 12) :=
  pointEquiv.symm.permCongrHom.toMonoidHom.comp modelAction

theorem literalAction_injective : Function.Injective literalAction :=
  pointEquiv.symm.permCongrHom.injective.comp modelAction_injective

def modelGenerators : Fin 2 → Model :=
  ![inl (Multiplicative.ofAdd (Pi.single (1 : Block) (1 : ZMod 3))),
    inr (Multiplicative.ofAdd 1)]

theorem generators_binding (i : Fin 2) :
    literalAction (modelGenerators i) = row131Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

private abbrev Generated : Subgroup Model := Subgroup.closure (Set.range modelGenerators)

private theorem inr_mem_generated (c : Block) : (inr c : Model) ∈ Generated := by
  have hc : (Multiplicative.ofAdd (1 : ZMod 4)) ^ c.toAdd.val = c := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_pow, nsmul_eq_mul]
  rw [← hc, map_pow]
  exact Generated.pow_mem (Subgroup.subset_closure (Set.mem_range_self (1 : Fin 2))) _

private theorem inl_single_mem_generated (c : Block) :
    (inl (Multiplicative.ofAdd (Pi.single c (1 : ZMod 3))) : Model) ∈ Generated := by
  have hrotate : rotation c (Multiplicative.ofAdd (Pi.single (1 : Block) (1 : ZMod 3))) =
      Multiplicative.ofAdd (Pi.single c 1) := by
    apply Multiplicative.toAdd.injective
    change permutationFunctionRepresentation (ZMod 3) Block Block c (Pi.single 1 1) = _
    simp only [permutationFunctionRepresentation_single, smul_eq_mul, mul_one, toAdd_ofAdd]
  rw [← hrotate, inl_aut]
  exact Generated.mul_mem
    (Generated.mul_mem (inr_mem_generated c)
      (Subgroup.subset_closure (Set.mem_range_self (0 : Fin 2))))
    (by simpa only [map_inv] using Generated.inv_mem (inr_mem_generated c))

private theorem translation_decomposition (v : Vector) :
    ∏ c : Block, Multiplicative.ofAdd (Pi.single c (1 : ZMod 3)) ^ (v c).val =
      Multiplicative.ofAdd v := by
  apply Multiplicative.toAdd.injective
  simp only [toAdd_prod, toAdd_pow,
    toAdd_ofAdd]
  calc
    (∑ c : Block, (v c).val • Pi.single c (1 : ZMod 3)) =
        ∑ c : Block, Pi.single c (v c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Pi.single_smul]
      congr 1
      simp [nsmul_eq_mul]
    _ = v := LinearMap.sum_single_apply (fun _ : Block ↦ ZMod 3) v

private theorem inl_mem_generated (v : Translation) : (inl v : Model) ∈ Generated := by
  let T : Subgroup Translation := Generated.comap (inl : Translation →* Model)
  change Multiplicative.ofAdd v.toAdd ∈ T
  rw [← translation_decomposition v.toAdd]
  apply T.prod_mem
  intro c _
  exact T.pow_mem (inl_single_mem_generated c) _

theorem model_generated : Subgroup.closure (Set.range modelGenerators) = ⊤ := by
  apply top_unique
  intro g _
  rw [← inl_left_mul_inr_right g]
  exact Generated.mul_mem (inl_mem_generated g.left) (inr_mem_generated g.right)

theorem literalAction_range : literalAction.range = Top := by
  apply le_antisymm
  · have hle : Generated ≤ Top.comap literalAction := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, rfl⟩
      change literalAction (modelGenerators i) ∈ Top
      rw [generators_binding]
      exact Subgroup.subset_closure (Set.mem_range_self i)
    rintro _ ⟨g, rfl⟩
    apply hle
    rw [show Generated = ⊤ from model_generated]
    exact Subgroup.mem_top g
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨modelGenerators i, generators_binding i⟩

def modelEquiv : Model ≃* Top :=
  (MonoidHom.ofInjective literalAction_injective).trans
    (MulEquiv.subgroupCongr literalAction_range)

def topAffineEquiv : Top ≃* AffineModel.Aff linearGroup :=
  modelEquiv.symm.trans affineEquiv

end PrimitiveAffineDegreeTwoTwelveRow131AffineModel
end SymmetricSubgroupAsymptotics

end
