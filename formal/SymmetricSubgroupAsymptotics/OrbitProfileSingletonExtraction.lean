import SymmetricSubgroupAsymptotics.OrbitProfileProduct
import SymmetricSubgroupAsymptotics.PGroupTransitiveDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Extract all original singleton occurrences with their exact factorial

A single degree-one color records all f original fixed points. Its local
action is the literal full permutation group on a singleton. Removing
these trivial coordinate groups preserves every remaining original
coordinate and its full projection. Whole-profile assembly then retains
the exact divisor f!, without iterating one-point upper bounds.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.OrbitProfileSingletonExtraction

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

def points : PUnit.{1} ⊕ α → Type
  | .inl _ => PUnit.{1}
  | .inr a => Ω a

instance (a : PUnit.{1} ⊕ α) : Fintype (points Ω a) := by
  cases a <;> dsimp [points] <;> infer_instance

instance (a : PUnit.{1} ⊕ α) : Nonempty (points Ω a) := by
  cases a <;> dsimp [points] <;> infer_instance

def action : (a : PUnit.{1} ⊕ α) → Subgroup (Equiv.Perm (points Ω a))
  | .inl _ => ⊤
  | .inr a => U a

instance (a : PUnit.{1}) : Subsingleton (points Ω (.inl a)) := by
  change Subsingleton PUnit.{1}
  infer_instance

instance (a : PUnit.{1}) : Subsingleton (action Ω U (.inl a)) := by
  change Subsingleton (⊤ : Subgroup (Equiv.Perm PUnit.{1}))
  infer_instance

def multiplicity (f : ℕ) : PUnit.{1} ⊕ α → ℕ
  | .inl _ => f
  | .inr a => m a

abbrev Original (f : ℕ) := OrbitProfileProductGroup (multiplicity m f) (action Ω U)
abbrev Remaining := OrbitProfileProductGroup m U
abbrev ModelPoints (f : ℕ) := OrbitProfilePoints (points Ω) (multiplicity m f)

/-- The inverse inserts only the identity actions on the original
singleton occurrences. Every other original coordinate is unchanged. -/
def productEquiv (f : ℕ) : Original Ω m U f ≃* Remaining Ω m U where
  toFun x a := x (.inr a)
  invFun x a := match a with
    | .inl _ => fun _ => 1
    | .inr a => x a
  left_inv x := by
    funext a j
    cases a with
    | inl a => exact Subsingleton.elim _ _
    | inr a => rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem productEquiv_original (f : ℕ) (x : Original Ω m U f)
    (a : α) (j : Fin (m a)) : productEquiv Ω m U f x a j = x (.inr a) j := rfl

/-- This is a literal original-point identity, not just an abstract
isomorphism or cardinality comparison. -/
theorem productAction_fixes (f : ℕ) (x : Original Ω m U f) (j : Fin f) :
    orbitProfileProductAction (multiplicity m f) (action Ω U) x
      ⟨.inl PUnit.unit,j,PUnit.unit⟩ = ⟨.inl PUnit.unit,j,PUnit.unit⟩ := by
  change (⟨.inl PUnit.unit,j,(x (.inl PUnit.unit) j).1 PUnit.unit⟩ :
    ModelPoints Ω m f) = _
  exact congrArg (fun z : PUnit.{1} =>
    (⟨.inl PUnit.unit,j,z⟩ : ModelPoints Ω m f)) (Subsingleton.elim _ _)

theorem full_map_iff (f : ℕ) (H : Subgroup (Original Ω m U f)) :
    OrbitProfileProductFull (multiplicity m f) (action Ω U) H ↔
      OrbitProfileProductFull m U (H.map (productEquiv Ω m U f).toMonoidHom) := by
  constructor
  · intro h a j u
    obtain ⟨x,hx⟩ := h (.inr a) j u
    exact ⟨⟨productEquiv Ω m U f x.1,⟨x.1,x.2,rfl⟩⟩,hx⟩
  · intro h a j u
    cases a with
    | inl a => exact ⟨1,Subsingleton.elim _ _⟩
    | inr a =>
      obtain ⟨y,hy⟩ := h a j u
      obtain ⟨x,hx,he⟩ := y.2
      exact ⟨⟨x,hx⟩,(congrArg (fun z : Remaining Ω m U => z a j) he).trans hy⟩

def fullProductEquiv (f : ℕ) :
    {H : Subgroup (Original Ω m U f) //
      OrbitProfileProductFull (multiplicity m f) (action Ω U) H} ≃
    {H : Subgroup (Remaining Ω m U) // OrbitProfileProductFull m U H} :=
  Equiv.subtypeEquiv (productEquiv Ω m U f).mapSubgroup.toEquiv
    (full_map_iff Ω m U f)

/-- Restriction and extension preserve the actual full model subgroup. -/
def fullModelEquiv (f : ℕ) :
    {H : Subgroup (Equiv.Perm (ModelPoints Ω m f)) //
      OrbitProfileFull (action Ω U) 1 H} ≃
    {H : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) // OrbitProfileFull U 1 H} :=
  (orbitProfileProductFullEquiv (multiplicity m f) (action Ω U)).symm.trans
    ((fullProductEquiv Ω m U f).trans (orbitProfileProductFullEquiv m U))

theorem action_transitive
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y) :
    ∀ a (x y : points Ω a), ∃ u : action Ω U a,
      (u : Equiv.Perm (points Ω a)) x = y := by
  intro a x y
  cases a with
  | inl a => exact ⟨1,Subsingleton.elim _ _⟩
  | inr a => exact htrans a x y

theorem point_card_singleton (a : PUnit.{1}) : Fintype.card (points Ω (.inl a)) = 1 := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_unique

theorem action_separated (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 1) :
    OrbitActionTypesSeparated (points Ω) (action Ω U) := by
  intro a b e hab hba
  cases a with
  | inl a =>
    cases b with
    | inl b => cases a; cases b; rfl
    | inr b =>
      exfalso
      apply hdegree b
      have h := (Fintype.card_congr e).symm
      cases a
      simpa only [point_card_singleton] using h
  | inr a =>
    cases b with
    | inl b =>
      exfalso
      apply hdegree a
      have h := Fintype.card_congr e
      cases b
      simpa only [point_card_singleton] using h
    | inr b => exact congrArg Sum.inr (hsep a b e hab hba)

def remainingDegree : ℕ := ∑ a, m a * Fintype.card (Ω a)
def remainingDenominator : ℚ :=
  ∏ a, (Nat.card (Subgroup.normalizer (U a : Set (Equiv.Perm (Ω a)))) : ℚ)^m a *
    (m a).factorial

theorem degree (f : ℕ) :
    (∑ a, multiplicity m f a * Fintype.card (points Ω a)) = f + remainingDegree Ω m := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_unique,multiplicity,point_card_singleton,mul_one]
  rfl

theorem denominator (f : ℕ) :
    (∏ a, (Nat.card (Subgroup.normalizer
      (action Ω U a : Set (Equiv.Perm (points Ω a)))) : ℚ)^multiplicity m f a *
        (multiplicity m f a).factorial) = f.factorial * remainingDenominator Ω m U := by
  have hs : Nat.card (Subgroup.normalizer
      (action Ω U (.inl PUnit.unit) : Set (Equiv.Perm (points Ω (.inl PUnit.unit))))) = 1 := by
    change Nat.card (Subgroup.normalizer
      ((⊤ : Subgroup (Equiv.Perm PUnit.{1})) : Set (Equiv.Perm PUnit.{1}))) = 1
    exact Nat.card_unique
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique,multiplicity,hs,Nat.cast_one,one_pow,one_mul]
  rfl

/-- Exact whole-family fixed-point extraction. The actual relabelled
remaining family is counted, with the original occurrence divisor f!. -/
theorem card_physical_rat (f : ℕ) {X Y : Type}
    (sourceChart : ModelPoints Ω m f ≃ X)
    (remainingChart : OrbitProfilePoints Ω m ≃ Y)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 1) :
    (Nat.card (FullOrbitProfileOn (points Ω) (multiplicity m f) (action Ω U) X) : ℚ) =
      ((f+remainingDegree Ω m).factorial : ℚ) /
        ((remainingDegree Ω m).factorial * f.factorial) *
          Nat.card (FullOrbitProfileOn Ω m U Y) := by
  have hs := fullOrbitProfileOn_card_rat (multiplicity m f) (action Ω U) sourceChart
    (action_transitive Ω U htrans) (action_separated Ω U hsep hdegree)
  have ht := fullOrbitProfileOn_card_rat m U remainingChart htrans hsep
  rw [degree Ω m f,denominator Ω m U f,
    Nat.card_congr (fullModelEquiv Ω m U f)] at hs
  rw [hs,ht]
  change ((f+remainingDegree Ω m).factorial : ℚ) * _ /
      (f.factorial * remainingDenominator Ω m U) =
    ((f+remainingDegree Ω m).factorial : ℚ) /
      ((remainingDegree Ω m).factorial * f.factorial) *
      (((remainingDegree Ω m).factorial : ℚ) * _ / remainingDenominator Ω m U)
  have hf : (f.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero f)
  have hd : ((remainingDegree Ω m).factorial : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hE : remainingDenominator Ω m U ≠ 0 := by
    apply ne_of_gt
    apply Finset.prod_pos
    intro a _
    exact mul_pos (pow_pos (Nat.cast_pos.mpr Nat.card_pos) _)
      (Nat.cast_pos.mpr (Nat.factorial_pos _))
  field_simp [hf,hd,hE] <;> ring

/-- Earlier ownership exclusions stay on the original subgroup. Removing
them uses inclusion, not an exact formula for an arbitrary predicate. -/
theorem card_restricted_physical_le (f : ℕ) {X Y : Type}
    (sourceChart : ModelPoints Ω m f ≃ X)
    (remainingChart : OrbitProfilePoints Ω m ≃ Y)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 1)
    (P : Subgroup (Equiv.Perm X) → Prop) :
    (Nat.card {H : FullOrbitProfileOn (points Ω) (multiplicity m f) (action Ω U) X //
      P H.1} : ℚ) ≤
      ((f+remainingDegree Ω m).factorial : ℚ) /
        ((remainingDegree Ω m).factorial * f.factorial) *
          Nat.card (FullOrbitProfileOn Ω m U Y) := by
  letI : Finite X := Finite.of_equiv (ModelPoints Ω m f) sourceChart
  letI : Finite (FullOrbitProfileOn (points Ω) (multiplicity m f) (action Ω U) X) := by
    unfold FullOrbitProfileOn
    infer_instance
  rw [← card_physical_rat Ω m U f sourceChart remainingChart htrans hsep hdegree]
  exact_mod_cast Nat.card_le_card_of_injective
    (fun H : {H : FullOrbitProfileOn (points Ω) (multiplicity m f) (action Ω U) X //
      P H.1} => H.1) Subtype.val_injective

/-- The remaining full action really has no common fixed point. -/
theorem remaining_fixedPointFree {Y : Type} (H : FullOrbitProfileOn Ω m U Y)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 1) :
    ∀ y : Y, ∃ h : H.1, (h : Equiv.Perm Y) y ≠ y := by
  obtain ⟨e,he⟩ := H.2
  intro y
  generalize hz : e.symm y = z
  rcases z with ⟨a,j,x⟩
  have hcard : 1 < Fintype.card (Ω a) := by
    have hpos : 0 < Fintype.card (Ω a) := Fintype.card_pos
    have hne := hdegree a
    omega
  letI : Nontrivial (Ω a) := (Finite.one_lt_card_iff_nontrivial).mp
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨x',hx'⟩ := exists_ne x
  obtain ⟨u,hu⟩ := htrans a x x'
  obtain ⟨h,hh⟩ := he.full a j u
  refine ⟨h,?_⟩
  have hy : e ⟨a,j,x⟩ = y := by rw [← hz,Equiv.apply_symm_apply]
  rw [← hy,hh x,hu]
  intro hxy
  have hsig := e.injective hxy
  have hp : (j,x') = (j,x) := by
    simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hsig
  exact hx' (congrArg Prod.snd hp)

/-- A binary transitive remaining action has even degree once the actual
singleton action color has been removed. -/
theorem remainingDegree_even (hU : ∀ a, IsPGroup 2 (U a))
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 1) : 2 ∣ remainingDegree Ω m := by
  apply Finset.dvd_sum
  intro a _
  obtain ⟨k,hk⟩ := pGroup_transitive_degree (hU a)
    (Classical.choice (inferInstance : Nonempty (Ω a)))
    (htrans a (Classical.choice (inferInstance : Nonempty (Ω a))))
  rw [Nat.card_eq_fintype_card] at hk
  have hkpos : 0 < k := by
    by_contra h
    have hkzero : k = 0 := by omega
    exact hdegree a (by simpa only [hkzero,pow_zero] using hk)
  rw [hk]
  exact dvd_mul_of_dvd_right (dvd_pow_self 2 (Nat.ne_of_gt hkpos)) _

/-- The empty remaining profile has exactly one model. This includes
zero original markers and a source consisting entirely of fixed points. -/
theorem card_physical_zero_remaining (f : ℕ) {X : Type}
    (sourceChart : ModelPoints Ω m f ≃ X) (hm : ∀ a, m a = 0)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 1) :
    Nat.card (FullOrbitProfileOn (points Ω) (multiplicity m f) (action Ω U) X) = 1 := by
  letI : Subsingleton (Remaining Ω m U) := ⟨by
    intro x y
    funext a j
    have hj := j.2
    have hz := hm a
    omega⟩
  letI : Subsingleton (Subgroup (Remaining Ω m U)) :=
    Subgroup.subsingleton_iff.mpr inferInstance
  have hfull : OrbitProfileProductFull m U (⊤ : Subgroup (Remaining Ω m U)) := by
    intro a j u
    have hj := j.2
    have hz := hm a
    omega
  have hmodel : Nat.card {H : Subgroup (Remaining Ω m U) // OrbitProfileProductFull m U H} = 1 :=
    Nat.card_eq_one_iff_exists.mpr ⟨⟨⊤,hfull⟩,fun _ => Subtype.ext (Subsingleton.elim _ _)⟩
  have hp := fullOrbitProfileOn_card_rat (multiplicity m f) (action Ω U) sourceChart
    (action_transitive Ω U htrans) (action_separated Ω U hsep hdegree)
  rw [degree Ω m f,denominator Ω m U f,
    Nat.card_congr (fullModelEquiv Ω m U f),← orbitProfileProductFull_card m U,hmodel] at hp
  have hd : remainingDegree Ω m = 0 := by simp [remainingDegree,hm]
  have hden : remainingDenominator Ω m U = 1 := by simp [remainingDenominator,hm]
  rw [hd,hden] at hp
  have hr : (Nat.card (FullOrbitProfileOn (points Ω) (multiplicity m f) (action Ω U) X) : ℚ) = 1 := by
    have hf : (f.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero f)
    simpa only [Nat.add_zero,Nat.cast_one,mul_one,div_self hf] using hp
  exact_mod_cast hr

end SymmetricSubgroupAsymptotics.OrbitProfileSingletonExtraction

end
