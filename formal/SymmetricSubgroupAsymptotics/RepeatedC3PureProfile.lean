import SymmetricSubgroupAsymptotics.RepeatedC3TailPhysical
import SymmetricSubgroupAsymptotics.OrbitProfileUpperWeights

/-!
# Original-weight profiles consisting only of regular C3 orbits

The empty-tail endpoint of simultaneous regular-C3 extraction is an honest
one-colour orbit profile.  Removing the artificial empty tail colour lets the
general profile theorem retain the exact divisor `6^c c!`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace RepeatedC3PureProfile

abbrev Color := PUnit.{1}

def points (_ : Color) : Type := TernaryCyclic

instance (i : Color) : Fintype (points i) := by
  cases i
  change Fintype TernaryCyclic
  infer_instance

instance (i : Color) : Nonempty (points i) := by
  cases i
  exact ⟨Multiplicative.ofAdd (0 : ZMod 3)⟩

def action (i : Color) : Subgroup (Equiv.Perm (points i)) := by
  cases i
  exact ternaryRegularAction

def multiplicity (c : ℕ) (_ : Color) : ℕ := c

abbrev ModelPoints (c : ℕ) :=
  OrbitProfilePoints (ι := Color) points (multiplicity c)
abbrev Product (c : ℕ) :=
  OrbitProfileProductGroup (ι := Color) (Ω := points) (multiplicity c) action

/-- Forget the unique colour coordinate. -/
def sourceEquiv (c : ℕ) :
    Product c ≃* TernaryProductGraphBound.Elementary c where
  toFun f := Multiplicative.ofAdd (fun j =>
    (ternaryRegularEquiv.symm (f PUnit.unit j)).toAdd)
  invFun z _ j := ternaryRegularEquiv (Multiplicative.ofAdd (z.toAdd j))
  left_inv f := by
    funext i j
    cases i
    exact ternaryRegularEquiv.apply_symm_apply _
  right_inv z := by
    apply Multiplicative.toAdd.injective
    funext j
    exact congrArg Multiplicative.toAdd
      (ternaryRegularEquiv.symm_apply_apply (Multiplicative.ofAdd (z.toAdd j)))
  map_mul' f g := by
    apply Multiplicative.toAdd.injective
    funext j
    change (ternaryRegularEquiv.symm
        (f PUnit.unit j * g PUnit.unit j)).toAdd =
      (ternaryRegularEquiv.symm (f PUnit.unit j)).toAdd +
        (ternaryRegularEquiv.symm (g PUnit.unit j)).toAdd
    exact congrArg Multiplicative.toAdd
      (map_mul ternaryRegularEquiv.symm _ _)

/-- Permutation models coming from a subgroup of the literal product of the
regular ternary actions. -/
def modelPredicate (c : ℕ)
    (K : Subgroup (Equiv.Perm (ModelPoints c))) : Prop :=
  ∃ H : Subgroup (Product c),
    H.map (orbitProfileProductAction (multiplicity c) action) = K

theorem modelPredicate_natural (c : ℕ) :
    OrbitProfileFamilyNatural points (multiplicity c) action
      (modelPredicate c) := by
  rintro w ⟨a, rfl⟩ K ⟨H, rfl⟩
  refine ⟨H.map (orbitProfileProductCoordinateEquiv a).toMonoidHom, ?_⟩
  exact (relabel_productAction_map_coordinate a H).symm

theorem model_card_le (c : ℕ) :
    Nat.card {K : Subgroup (Equiv.Perm (ModelPoints c)) //
        modelPredicate c K} ≤
      (c + 1) * 3 ^ (c * c / 4 + c) := by
  let Source := Subgroup (Product c)
  let f : Source → {K : Subgroup (Equiv.Perm (ModelPoints c)) //
      modelPredicate c K} := fun H =>
    ⟨H.map (orbitProfileProductAction (multiplicity c) action), H, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨K, H, rfl⟩
    exact ⟨H, rfl⟩
  have hsource : Nat.card Source =
      Nat.card (Submodule (ZMod 3) (TernaryProductGraphBound.Space c)) := by
    calc
      Nat.card Source =
          Nat.card (Subgroup (TernaryProductGraphBound.Elementary c)) :=
        Nat.card_congr (sourceEquiv c).mapSubgroup
      _ = _ := Nat.card_congr
        (TernaryProductGraphBound.subgroupOrderIso c).symm.toEquiv
  calc
    _ ≤ Nat.card Source := Nat.card_le_card_of_surjective f hf
    _ = _ := hsource
    _ ≤ _ := TernaryProductGraphBound.submodule_card_le c

/-- Exact original-action weight of the pure regular-C3 profile. -/
theorem assembled_card_le (c : ℕ) {X : Type}
    (e : ModelPoints c ≃ X) :
    (Nat.card (AssembledOrbitProfileOn (modelPredicate c) X) : ℝ) ≤
      ((3 * c).factorial : ℝ) *
        ((c + 1 : ℕ) * 3 ^ (c * c / 4 + c)) := by
  have hmodel :
      (Nat.card {K : Subgroup (Equiv.Perm (ModelPoints c)) //
          modelPredicate c K} : ℝ) ≤
        ((c + 1 : ℕ) * 3 ^ (c * c / 4 + c) : ℕ) := by
    exact_mod_cast model_card_le c
  have hdegree :
      (∑ i, multiplicity c i * Fintype.card (points i)) = 3 * c := by
    simp only [Fintype.sum_unique, multiplicity]
    change c * Fintype.card TernaryCyclic = 3 * c
    norm_num [TernaryCyclic]
    omega
  have h :
      (Nat.card (AssembledOrbitProfileOn (modelPredicate c) X) : ℝ) ≤
        ((∑ i, multiplicity c i * Fintype.card (points i)).factorial : ℝ) *
          (((c + 1) * 3 ^ (c * c / 4 + c) : ℕ) : ℝ) /
            (∏ i, (Nat.card (Subgroup.normalizer
              (action i : Set (Equiv.Perm (points i)))) : ℝ) ^ multiplicity c i *
                ((multiplicity c i).factorial : ℝ)) :=
    assembledOrbitProfileOn_card_le_real_of_model_bound
      (modelPredicate_natural c) e hmodel
  rw [hdegree] at h
  simp only [Fintype.prod_unique, multiplicity] at h
  rw [show action default = ternaryRegularAction by rfl] at h
  have hden : (1 : ℝ) ≤
      (Nat.card (Subgroup.normalizer
        (ternaryRegularAction : Set (Equiv.Perm TernaryCyclic))) : ℝ) ^ c *
          (c.factorial : ℝ) := by
    have hnormalizerR : (1 : ℝ) ≤ Nat.card (Subgroup.normalizer
        (ternaryRegularAction : Set (Equiv.Perm TernaryCyclic))) := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card (Subgroup.normalizer
        (ternaryRegularAction : Set (Equiv.Perm TernaryCyclic))))
    have hfacR : (1 : ℝ) ≤ c.factorial := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos c)
    calc
      1 = 1 ^ c * 1 := by simp
      _ ≤ (Nat.card (Subgroup.normalizer
            (ternaryRegularAction : Set (Equiv.Perm TernaryCyclic))) : ℝ) ^ c *
          (c.factorial : ℝ) :=
        mul_le_mul (pow_le_pow_left₀ (by norm_num) hnormalizerR c)
          hfacR (by norm_num) (by positivity)
  have hquot :
      ((3 * c).factorial : ℝ) *
          (((c + 1) * 3 ^ (c * c / 4 + c) : ℕ) : ℝ) /
        ((Nat.card (Subgroup.normalizer
          (ternaryRegularAction : Set (Equiv.Perm TernaryCyclic))) : ℝ) ^ c *
            (c.factorial : ℝ)) ≤
      ((3 * c).factorial : ℝ) *
          (((c + 1) * 3 ^ (c * c / 4 + c) : ℕ) : ℝ) :=
    div_le_self (by positivity) hden
  have hfinal :
      (Nat.card (AssembledOrbitProfileOn (modelPredicate c) X) : ℝ) ≤
        ((3 * c).factorial : ℝ) *
          (((c + 1) * 3 ^ (c * c / 4 + c) : ℕ) : ℝ) :=
    h.trans hquot
  norm_num at hfinal ⊢
  exact hfinal

/-- The pure point set is the left summand of a tail profile whose tail is
certified void. -/
def toVoidTailPoints (c m : ℕ) (void : Fin 0 ≃ Fin m) :
    ModelPoints c ≃ RepeatedC3TailProfile.ModelPoints c m where
  toFun z := ⟨Sum.inl PUnit.unit, z.2.1, z.2.2⟩
  invFun z := by
    rcases z with ⟨i,j,x⟩
    cases i with
    | inl u => exact ⟨PUnit.unit,j,x⟩
    | inr u => exact Fin.elim0 (void.symm x)
  left_inv z := by rcases z with ⟨i,j,x⟩; cases i; rfl
  right_inv z := by
    rcases z with ⟨i,j,x⟩
    cases i with
    | inl u => cases u; rfl
    | inr u => exact Fin.elim0 (void.symm x)

/-- Forgetting the void tail identifies the two literal product groups. -/
def toVoidTailProduct (c m : ℕ) (void : Fin 0 ≃ Fin m) :
    Product c ≃* RepeatedC3TailProfile.Product c m where
  toFun f i := by
    cases i with
    | inl u => cases u; exact f PUnit.unit
    | inr u => cases u; exact fun _ => 1
  invFun f _ := f (Sum.inl PUnit.unit)
  left_inv f := by funext i j; cases i; rfl
  right_inv f := by
    funext i j
    cases i with
    | inl u => cases u; rfl
    | inr u =>
        cases u
        apply Subtype.ext
        apply Equiv.ext
        intro x
        exact Fin.elim0 (void.symm x)
  map_mul' f g := by
    funext i j
    cases i with
    | inl u => cases u; rfl
    | inr u => cases u; rfl

theorem toVoidTailProduct_action (c m : ℕ) (void : Fin 0 ≃ Fin m)
    (f : Product c) :
    orbitProfileProductAction (RepeatedC3TailProfile.multiplicity c)
        (RepeatedC3TailProfile.action m) (toVoidTailProduct c m void f) =
      (toVoidTailPoints c m void).permCongr
        (orbitProfileProductAction (multiplicity c) action f) := by
  apply Equiv.ext
  intro z
  rcases z with ⟨i,j,x⟩
  cases i with
  | inl u => cases u; rfl
  | inr u => exact Fin.elim0 (void.symm x)

/-- If the simultaneous extraction has empty tail, its original physical
subgroup belongs to the pure one-colour assembled profile. -/
noncomputable def assembled_of_tailDegree_zero
    {X : Type} [Fintype X]
    (G : Subgroup (Equiv.Perm X))
    (hm : RepeatedC3TailPhysical.tailDegree G = 0) :
    AssembledOrbitProfileOn
      (modelPredicate (RepeatedC3TailPhysical.regularCount G)) X := by
  let c := RepeatedC3TailPhysical.regularCount G
  let m := RepeatedC3TailPhysical.tailDegree G
  let void : Fin 0 ≃ Fin m := finCongr hm.symm
  let e0 := toVoidTailPoints c m void
  let eTail : RepeatedC3TailProfile.ModelPoints c m ≃ X :=
    RepeatedC3TailPhysical.chart G
  let e : ModelPoints c ≃ X := e0.trans eTail
  let Htail : Subgroup (RepeatedC3TailProfile.Product c m) :=
    RepeatedC3TailPhysical.modelSubgroup G
  let H : Subgroup (Product c) :=
    Htail.comap (toVoidTailProduct c m void).toMonoidHom
  let K := H.map (orbitProfileProductAction (multiplicity c) action)
  refine ⟨G, e, K, ⟨H, rfl⟩, ?_⟩
  have hmap : H.map (toVoidTailProduct c m void).toMonoidHom = Htail := by
    apply Subgroup.map_comap_eq_self
    intro y hy
    obtain ⟨x, rfl⟩ := (toVoidTailProduct c m void).surjective y
    exact ⟨x, rfl⟩
  have haction : relabelSubgroup e0
      (H.map (orbitProfileProductAction (multiplicity c) action)) =
        Htail.map (orbitProfileProductAction
          (RepeatedC3TailProfile.multiplicity c)
          (RepeatedC3TailProfile.action m)) := by
    change (H.map _).map e0.permCongrHom.toMonoidHom = _
    rw [← hmap, Subgroup.map_map, Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro f
    exact (toVoidTailProduct_action c m void f).symm
  change relabelSubgroup e K = G
  rw [show e = e0.trans eTail by rfl, ← relabelSubgroup_trans]
  change relabelSubgroup eTail
      (relabelSubgroup e0
        (H.map (orbitProfileProductAction (multiplicity c) action))) = G
  rw [haction]
  have hphysical : Htail.map (orbitProfileProductAction
      (RepeatedC3TailProfile.multiplicity c)
      (RepeatedC3TailProfile.action m)) =
        relabelSubgroup eTail.symm G := by
    dsimp only [Htail, eTail, c]
    exact RepeatedC3TailPhysical.modelSubgroup_action G
  rw [hphysical]
  exact relabelSubgroup_symm eTail.symm G

end RepeatedC3PureProfile
end SymmetricSubgroupAsymptotics

end
