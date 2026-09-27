import SymmetricSubgroupAsymptotics.RepeatedOddMarkerImageSum
import SymmetricSubgroupAsymptotics.OrbitProfileProductSum

/-!
# Exact physical profiles with repeated original S3 markers

The whole original full-profile family is assembled before its model
cardinality is expanded over contraction images. Every original marker
has normalizer six and all g occurrences have the original divisor g!.
The exterior actions, their multiplicities, and all their individual
fullness conditions remain unchanged. No fixed-image fibre is separately
divided by a physical normalizer, and no desired count is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedOddMarkerPhysicalProfile

open RepeatedOddMarkerKernel
open RepeatedOddMarkerIsotypeCount DiagonalInvariantSubmodules DiagonalFullSubmoduleWeights

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a))) (g : ℕ)

abbrev Exterior := OrbitProfileProductGroup m U

def points : PUnit.{1} ⊕ α → Type
  | .inl _ => Fin 3
  | .inr a => Ω a

instance (a : PUnit.{1} ⊕ α) : Fintype (points Ω a) := by
  cases a <;> dsimp [points] <;> infer_instance

instance (a : PUnit.{1} ⊕ α) : Nonempty (points Ω a) := by
  cases a <;> dsimp [points] <;> infer_instance

def action : (a : PUnit.{1} ⊕ α) → Subgroup (Equiv.Perm (points Ω a))
  | .inl _ => oddMarkerActionSubgroup
  | .inr a => U a

def multiplicity : PUnit.{1} ⊕ α → ℕ
  | .inl _ => g
  | .inr a => m a

abbrev ModelPoints := OrbitProfilePoints (points Ω) (multiplicity m g)
abbrev Original := (Fin g → OddMarkerGroup) × Exterior Ω m U

/-- Remove only the unique marker-color tag and the top-subgroup wrapper.
Every original marker occurrence and exterior coordinate is retained. -/
def productEquiv : OrbitProfileProductGroup (multiplicity m g) (action Ω U) ≃*
    Original Ω m U g where
  toFun f := (fun j => (f (.inl PUnit.unit) j).1, fun a => f (.inr a))
  invFun f a := match a with
    | .inl _ => fun j => ⟨f.1 j, Subgroup.mem_top _⟩
    | .inr a => f.2 a
  left_inv f := by
    funext a j
    cases a with
    | inl a => cases a; rfl
    | inr a => rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def OriginalFull (H : Subgroup (Original Ω m U g)) : Prop :=
  (∀ j, H.map (coordinate j) = ⊤) ∧
    OrbitProfileProductFull m U (H.map (MonoidHom.snd _ _))

/-- Fullness concerns each original orbit, not the entire exterior product. -/
theorem full_comap_iff (H : Subgroup (Original Ω m U g)) :
    OrbitProfileProductFull (multiplicity m g) (action Ω U)
      (H.comap (productEquiv Ω m U g).toMonoidHom) ↔ OriginalFull Ω m U g H := by
  constructor
  · intro h
    constructor
    · intro j
      apply top_unique
      intro u _
      obtain ⟨x,hx⟩ := h (.inl PUnit.unit) j ⟨u,Subgroup.mem_top _⟩
      exact Subgroup.mem_map.mpr ⟨productEquiv Ω m U g x.1,x.2,
        congrArg Subtype.val hx⟩
    · intro a j u
      obtain ⟨x,hx⟩ := h (.inr a) j u
      exact ⟨⟨(productEquiv Ω m U g x.1).2,
        Subgroup.mem_map.mpr ⟨productEquiv Ω m U g x.1,x.2,rfl⟩⟩,hx⟩
  · rintro ⟨hmarker,hexterior⟩ a j u
    cases a with
    | inl a =>
      cases a
      change Fin g at j
      change oddMarkerActionSubgroup at u
      have hu : u.1 ∈ H.map (coordinate (D := Exterior Ω m U) j) := by
        exact (hmarker j).symm ▸ Subgroup.mem_top u.1
      obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp hu
      refine ⟨⟨(productEquiv Ω m U g).symm x,?_⟩,?_⟩
      · change productEquiv Ω m U g ((productEquiv Ω m U g).symm x) ∈ H
        rw [MulEquiv.apply_symm_apply]
        exact hx
      · apply Subtype.ext
        exact he
    | inr a =>
      obtain ⟨y,hy⟩ := hexterior a j u
      obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp y.2
      refine ⟨⟨(productEquiv Ω m U g).symm x,?_⟩,?_⟩
      · change productEquiv Ω m U g ((productEquiv Ω m U g).symm x) ∈ H
        rw [MulEquiv.apply_symm_apply]
        exact hx
      · exact (congrArg (fun d : Exterior Ω m U => d a j) he).trans hy

def originalProductEquiv :
    {H : Subgroup (Original Ω m U g) // OriginalFull Ω m U g H} ≃
      {K : Subgroup (OrbitProfileProductGroup (multiplicity m g) (action Ω U)) //
        OrbitProfileProductFull (multiplicity m g) (action Ω U) K} where
  toFun H := ⟨H.1.comap (productEquiv Ω m U g).toMonoidHom,
    (full_comap_iff Ω m U g H.1).mpr H.2⟩
  invFun K := ⟨K.1.map (productEquiv Ω m U g).toMonoidHom,
    (full_comap_iff Ω m U g _).mp (by
      rw [Subgroup.comap_map_eq_self_of_injective (productEquiv Ω m U g).injective]
      exact K.2)⟩
  left_inv H := by
    apply Subtype.ext
    exact Subgroup.map_comap_eq_self_of_surjective (productEquiv Ω m U g).surjective H.1
  right_inv K := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective (productEquiv Ω m U g).injective K.1

/-- The predicate is on the same actual sign/exterior image, and retains
fullness on every original exterior occurrence. -/
def imagePredicate (B : Subgroup ((Fin g → Multiplicative (ZMod 2)) × Exterior Ω m U)) : Prop :=
  OrbitProfileProductFull m U (B.map (MonoidHom.snd _ _))

def originalImageEquiv :
    {H : Subgroup (Original Ω m U g) // OriginalFull Ω m U g H} ≃
      RepeatedOddMarkerImageSum.Family (imagePredicate Ω m U g) :=
  Equiv.subtypeEquivRight (fun H => by
    change ((∀ j, H.map (coordinate j)=⊤) ∧
      OrbitProfileProductFull m U (H.map (MonoidHom.snd _ _))) ↔
      ((∀ j, H.map (coordinate j)=⊤) ∧
        OrbitProfileProductFull m U ((H.map contraction).map (MonoidHom.snd _ _)))
    rw [RepeatedOddMarkerImageSum.exterior_projection])

/-- The entire full-profile model, before any physical quotient, is
identified with the whole original image family. -/
def modelImageEquiv :
    {K : Subgroup (Equiv.Perm (ModelPoints Ω m g)) //
      OrbitProfileFull (action Ω U) 1 K} ≃
      RepeatedOddMarkerImageSum.Family (imagePredicate Ω m U g) :=
  (orbitProfileProductFullEquiv (multiplicity m g) (action Ω U)).symm.trans
    ((originalProductEquiv Ω m U g).symm.trans (originalImageEquiv Ω m U g))

def modelWeight : ℚ :=
  RepeatedOddMarkerImageSum.familyWeight (imagePredicate Ω m U g)

theorem model_card (hD : IsPGroup 2 (Exterior Ω m U)) :
    (Nat.card {K : Subgroup (Equiv.Perm (ModelPoints Ω m g)) //
      OrbitProfileFull (action Ω U) 1 K} : ℚ) = modelWeight Ω m U g := by
  calc
    (Nat.card {K : Subgroup (Equiv.Perm (ModelPoints Ω m g)) //
      OrbitProfileFull (action Ω U) 1 K} : ℚ) =
        (Nat.card (RepeatedOddMarkerImageSum.Family (imagePredicate Ω m U g)) : ℚ) :=
      congrArg (fun n : ℕ => (n : ℚ)) (Nat.card_congr (modelImageEquiv Ω m U g))
    _ = modelWeight Ω m U g :=
      RepeatedOddMarkerImageSum.card_family_weight_rat hD (imagePredicate Ω m U g)

def exteriorDenominator : ℚ :=
  ∏ a, (Nat.card (Subgroup.normalizer (U a : Set (Equiv.Perm (Ω a)))) : ℚ) ^ m a *
    (m a).factorial

theorem originalDenominator :
    (∏ a, (Nat.card (Subgroup.normalizer
      (action Ω U a : Set (Equiv.Perm (points Ω a)))) : ℚ) ^ multiplicity m g a *
        (multiplicity m g a).factorial) =
      (6 : ℚ)^g * g.factorial * exteriorDenominator Ω m U := by
  have hmarker : Nat.card (Subgroup.normalizer
      (action Ω U (.inl PUnit.unit) : Set (Equiv.Perm (points Ω (.inl PUnit.unit))))) = 6 := by
    change Nat.card (Subgroup.normalizer
      (oddMarkerActionSubgroup : Set (Equiv.Perm (Fin 3)))) = 6
    exact oddMarker_normalizer_card
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique,multiplicity,hmarker,Nat.cast_ofNat]
  change (6 : ℚ)^g * g.factorial * exteriorDenominator Ω m U =
    (6 : ℚ)^g * g.factorial * exteriorDenominator Ω m U
  rfl

theorem physicalDegree :
    (∑ a, multiplicity m g a * Fintype.card (points Ω a)) =
      3*g + ∑ a, m a * Fintype.card (Ω a) := by
  have hmarker : Fintype.card (points Ω (.inl PUnit.unit)) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_fin 3
  rw [Fintype.sum_sum_type]
  simpa only [Fintype.sum_unique,multiplicity,hmarker] using
    congrArg (fun n => n + ∑ a, m a * Fintype.card (Ω a)) (Nat.mul_comm g 3)

theorem action_transitive
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x=y) :
    ∀ a (x y : points Ω a), ∃ u : action Ω U a,
      (u : Equiv.Perm (points Ω a)) x=y := by
  intro a
  cases a with
  | inl a => exact oddMarker_transitive
  | inr a => exact htrans a

/-- Original action types stay separated; the new marker has degree
three, explicitly different from every exterior degree. -/
theorem action_separated (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 3) :
    OrbitActionTypesSeparated (points Ω) (action Ω U) := by
  intro a b e hab hba
  cases a with
  | inl a =>
    cases b with
    | inl b => cases a; cases b; rfl
    | inr b =>
      exfalso
      apply hdegree b
      simpa only [points,Fintype.card_fin] using (Fintype.card_congr e).symm
  | inr a =>
    cases b with
    | inl b =>
      exfalso
      apply hdegree a
      simpa only [points,Fintype.card_fin] using Fintype.card_congr e
    | inr b => exact congrArg Sum.inr (hsep a b e hab hba)

abbrev PhysicalFamily (X : Type) :=
  FullOrbitProfileOn (points Ω) (multiplicity m g) (action Ω U) X

/-- Exact assembly of the whole original profile. The full family has
the required naturality by the existing generic theorem. The marker
divisor is 6^g g!, and every exterior normalizer remains original. -/
theorem card_physical_rat {X : Type}
    (e : ModelPoints Ω m g ≃ X) (hD : IsPGroup 2 (Exterior Ω m U))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x=y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 3) :
    (Nat.card (PhysicalFamily Ω m U g X) : ℚ) =
      ((3*g + ∑ a, m a * Fintype.card (Ω a)).factorial : ℚ) * modelWeight Ω m U g /
        ((6 : ℚ)^g * g.factorial * exteriorDenominator Ω m U) := by
  have h := fullOrbitProfileOn_card_rat (multiplicity m g) (action Ω U) e
    (action_transitive Ω U htrans) (action_separated Ω U hsep hdegree)
  rw [physicalDegree Ω m g, originalDenominator Ω m U g, model_card Ω m U g hD] at h
  exact h

end SymmetricSubgroupAsymptotics.RepeatedOddMarkerPhysicalProfile

end
