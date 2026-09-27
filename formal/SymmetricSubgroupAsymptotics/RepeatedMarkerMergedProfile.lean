import SymmetricSubgroupAsymptotics.RepeatedMarkerPairMerge
import SymmetricSubgroupAsymptotics.OrbitProfileReindexedProduct
import SymmetricSubgroupAsymptotics.OddCriticalProfiles

/-!
# The actual original two-point color in a merged marker profile

The retained scalar signs are installed in the checked original critical
C2 action. They are merged with the preexisting occurrences of that same
color. All other original actions and all their individual projections
are retained. The physical count is the existing exact natural-profile
count, with the actual pair normalizer two and one occurrence factorial.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.RepeatedMarkerMergedProfile

open RepeatedCharacterCollapse

variable {α : Type} [Fintype α] (Ω : α → Type)
    [∀ a, Fintype (Ω a)] [∀ a, Nonempty (Ω a)]
    (m : α → ℕ) (U : ∀ a, Subgroup (Equiv.Perm (Ω a)))

abbrev Sign := Multiplicative (ZMod 2)
abbrev Exterior := OrbitProfileProductGroup m U

def points : PUnit.{1} ⊕ α → Type
  | .inl _ => criticalActionPoints .c2
  | .inr a => Ω a

instance (a : PUnit.{1} ⊕ α) : Fintype (points Ω a) := by
  cases a <;> dsimp [points] <;> infer_instance

instance (a : PUnit.{1} ⊕ α) : Nonempty (points Ω a) := by
  cases a <;> dsimp [points] <;> infer_instance

def action : (a : PUnit.{1} ⊕ α) → Subgroup (Equiv.Perm (points Ω a))
  | .inl _ => criticalActionSubgroup .c2
  | .inr a => U a

def multiplicity (p : ℕ) : PUnit.{1} ⊕ α → ℕ
  | .inl _ => p
  | .inr a => m a

abbrev Original (p : ℕ) := OrbitProfileProductGroup (multiplicity m p) (action Ω U)
abbrev ModelPoints (p : ℕ) := OrbitProfilePoints (points Ω) (multiplicity m p)

/-- The scalar chart is the checked original critical C2 action chart. -/
def productEquiv (p : ℕ) : Original Ω m U p ≃* ((Fin p → Sign) × Exterior Ω m U) where
  toFun f := (fun j => binaryMarkerLocalEquiv.symm (f (.inl PUnit.unit) j),
    fun a => f (.inr a))
  invFun f a := match a with
    | .inl _ => fun j => binaryMarkerLocalEquiv (f.1 j)
    | .inr a => f.2 a
  left_inv f := by
    funext a j
    cases a with
    | inl a => cases a; exact binaryMarkerLocalEquiv.apply_symm_apply _
    | inr a => rfl
  right_inv f := by
    apply Prod.ext
    · funext j
      exact binaryMarkerLocalEquiv.symm_apply_apply _
    · rfl
  map_mul' f g := by
    apply Prod.ext
    · funext j
      exact binaryMarkerLocalEquiv.symm.map_mul _ _
    · rfl

/-- Merge the new q signs and the p actual old pair occurrences. The
entire original exterior element is carried through the chart. -/
def retainedChart (q p : ℕ) :
    ((Fin q → Sign) × Original Ω m U p) ≃* Original Ω m U (q+p) :=
  ((MulEquiv.refl (Fin q → Sign)).prodCongr (productEquiv Ω m U p)).trans
    ((RepeatedMarkerPairMerge.merge q p).trans (productEquiv Ω m U (q+p)).symm)

@[simp] theorem retainedChart_new (q p : ℕ)
    (x : (Fin q → Sign) × Original Ω m U p) (i : Fin q) :
    retainedChart Ω m U q p x (.inl PUnit.unit) (Fin.castAdd p i) =
      binaryMarkerLocalEquiv (x.1 i) := by
  change binaryMarkerLocalEquiv (Fin.addCases x.1
    (fun j => binaryMarkerLocalEquiv.symm (x.2 (.inl PUnit.unit) j))
    (Fin.castAdd p i)) = _
  simp

@[simp] theorem retainedChart_old (q p : ℕ)
    (x : (Fin q → Sign) × Original Ω m U p) (j : Fin p) :
    retainedChart Ω m U q p x (.inl PUnit.unit) (Fin.natAdd q j) =
      x.2 (.inl PUnit.unit) j := by
  change binaryMarkerLocalEquiv (Fin.addCases x.1
    (fun j => binaryMarkerLocalEquiv.symm (x.2 (.inl PUnit.unit) j))
    (Fin.natAdd q j)) = _
  simp

@[simp] theorem retainedChart_exterior (q p : ℕ)
    (x : (Fin q → Sign) × Original Ω m U p) (a : α) (j : Fin (m a)) :
    retainedChart Ω m U q p x (.inr a) j = x.2 (.inr a) j := rfl

/-- Every original coordinate projection is retained, without requiring
surjectivity onto the whole exterior product. -/
theorem retainedChart_full (q p : ℕ)
    (Y : Subgroup ((Fin q → Sign) × Original Ω m U p))
    (hnew : ∀ i, Function.Surjective (character Y i))
    (hOld : OrbitProfileProductFull (multiplicity m p) (action Ω U)
      (Y.map (MonoidHom.snd _ _))) :
    OrbitProfileProductFull (multiplicity m (q+p)) (action Ω U)
      (Y.map (retainedChart Ω m U q p).toMonoidHom) := by
  intro a j u
  cases a with
  | inl a =>
    cases a
    change Fin (q+p) at j
    change criticalActionSubgroup .c2 at u
    refine Fin.addCases ?_ ?_ j
    · intro i
      obtain ⟨x, hx⟩ := hnew i (binaryMarkerLocalEquiv.symm u)
      refine ⟨⟨retainedChart Ω m U q p x.1, ⟨x.1, x.2, rfl⟩⟩, ?_⟩
      change retainedChart Ω m U q p x.1 (.inl PUnit.unit) (Fin.castAdd p i) = u
      rw [retainedChart_new]
      change x.1.1 i = binaryMarkerLocalEquiv.symm u at hx
      rw [hx, binaryMarkerLocalEquiv.apply_symm_apply]
    · intro j
      obtain ⟨v, hv⟩ := hOld (.inl PUnit.unit) j u
      obtain ⟨x, hx, he⟩ := v.2
      refine ⟨⟨retainedChart Ω m U q p x, ⟨x, hx, rfl⟩⟩, ?_⟩
      change retainedChart Ω m U q p x (.inl PUnit.unit) (Fin.natAdd q j) = u
      rw [retainedChart_old]
      exact (congrArg (fun d : Original Ω m U p => d (.inl PUnit.unit) j) he).trans hv
  | inr a =>
    obtain ⟨v, hv⟩ := hOld (.inr a) j u
    obtain ⟨x, hx, he⟩ := v.2
    refine ⟨⟨retainedChart Ω m U q p x, ⟨x, hx, rfl⟩⟩, ?_⟩
    change x.2 (.inr a) j = u
    exact (congrArg (fun d : Original Ω m U p => d (.inr a) j) he).trans hv

theorem action_transitive
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y) :
    ∀ a (x y : points Ω a), ∃ u : action Ω U a,
      (u : Equiv.Perm (points Ω a)) x = y := by
  intro a
  cases a with
  | inl _ => exact criticalAction_transitive .c2
  | inr a => exact htrans a

theorem point_card_pair : Fintype.card (points Ω (.inl PUnit.unit)) = 2 := by
  rw [← Nat.card_eq_fintype_card]
  change Nat.card (criticalActionPoints .c2) = 2
  rw [Nat.card_eq_fintype_card, criticalAction_point_card]
  rfl

theorem action_separated (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
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
      simpa only [point_card_pair] using h
  | inr a =>
    cases b with
    | inl b =>
      exfalso
      apply hdegree a
      have h := Fintype.card_congr e
      cases b
      simpa only [point_card_pair] using h
    | inr b => exact congrArg Sum.inr (hsep a b e hab hba)

def exteriorDenominator : ℚ :=
  ∏ a, (Nat.card (Subgroup.normalizer (U a : Set (Equiv.Perm (Ω a)))) : ℚ)^m a *
    (m a).factorial

def exteriorDegree : ℕ := ∑ a, m a * Fintype.card (Ω a)

theorem denominator (p : ℕ) :
    (∏ a, (Nat.card (Subgroup.normalizer
      (action Ω U a : Set (Equiv.Perm (points Ω a)))) : ℚ)^multiplicity m p a *
        (multiplicity m p a).factorial) =
      (2 : ℚ)^p * p.factorial * exteriorDenominator Ω m U := by
  have hp : Nat.card (Subgroup.normalizer
      (action Ω U (.inl PUnit.unit) : Set (Equiv.Perm (points Ω (.inl PUnit.unit))))) = 2 := by
    change Nat.card (Subgroup.normalizer
      (criticalActionSubgroup .c2 : Set (Equiv.Perm (criticalActionPoints .c2)))) = 2
    exact criticalAction_normalizer_card .c2
  rw [Fintype.prod_sum_type]
  simp only [Fintype.prod_unique, multiplicity, hp, Nat.cast_ofNat]
  change (2 : ℚ)^p * p.factorial * exteriorDenominator Ω m U = _
  rfl

theorem degree (p : ℕ) :
    (∑ a, multiplicity m p a * Fintype.card (points Ω a)) =
      2*p + exteriorDegree Ω m := by
  rw [Fintype.sum_sum_type]
  simpa only [Fintype.sum_unique, multiplicity, point_card_pair] using
    congrArg (fun n => n + exteriorDegree Ω m) (Nat.mul_comm p 2)

/-- Exact merged physical profile: the actual allowed subgroup cardinality
is supplied by the original product-action equivalence, not as a premise. -/
theorem card_physical_rat (q p : ℕ)
    (P : Subgroup (Equiv.Perm (ModelPoints Ω m (q+p))) → Prop)
    {X : Type} (chart : ModelPoints Ω m (q+p) ≃ X)
    (hP : OrbitProfileFamilyNatural (points Ω) (multiplicity m (q+p)) (action Ω U) P)
    (htrans : ∀ a (x y : Ω a), ∃ u : U a, (u : Equiv.Perm (Ω a)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U)
    (hdegree : ∀ a, Fintype.card (Ω a) ≠ 2) :
    (Nat.card (OrbitProfileReindexedProduct.PhysicalFamily
      (multiplicity m (q+p)) (action Ω U) P X) : ℚ) =
      ((2*(q+p) + exteriorDegree Ω m).factorial : ℚ) *
        Nat.card (OrbitProfileReindexedProduct.ModelFamily (multiplicity m (q+p))
          (action Ω U) (retainedChart Ω m U q p) P) /
        ((2 : ℚ)^(q+p) * (q+p).factorial * exteriorDenominator Ω m U) := by
  have h := OrbitProfileReindexedProduct.card_physical_rat
    (multiplicity m (q+p)) (action Ω U) (retainedChart Ω m U q p) P chart hP
    (action_transitive Ω U htrans) (action_separated Ω U hsep hdegree)
  rw [degree Ω m, denominator Ω m U] at h
  exact h

end SymmetricSubgroupAsymptotics.RepeatedMarkerMergedProfile

end
