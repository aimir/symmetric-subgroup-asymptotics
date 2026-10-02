import SymmetricSubgroupAsymptotics.OrbitProfileProductConjugation
import SymmetricSubgroupAsymptotics.OrbitProfileUpperWeights
import SymmetricSubgroupAsymptotics.OrbitProfileProductSum
import SymmetricSubgroupAsymptotics.TernaryProductGraphBound
import SymmetricSubgroupAsymptotics.C1LowNaturality
import SymmetricSubgroupAsymptotics.C1PhysicalWeight

/-!
# Original-weight profiles with every regular C3 orbit extracted

There are `c` unordered regular `C3` blocks and one merged tail block of
size `m`.  The tail action in the atlas is the full symmetric group, so its
normalizer contributes exactly `m!`; the model predicate itself retains the
actual tail subgroup and its ternary-rank cap.  Fullness on the merged tail
is neither asserted nor needed by the upper-assembly theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace RepeatedC3TailProfile

abbrev Color := PUnit.{1} ⊕ PUnit.{1}

def points (m : ℕ) : Color → Type
  | .inl _ => TernaryCyclic
  | .inr _ => Fin m

instance (m : ℕ) (i : Color) : Fintype (points m i) := by
  cases i <;> simp only [points] <;> infer_instance

instance (m : ℕ) [NeZero m] (i : Color) : Nonempty (points m i) := by
  cases i with
  | inl u =>
      cases u
      change Nonempty TernaryCyclic
      exact ⟨Multiplicative.ofAdd (0 : ZMod 3)⟩
  | inr u =>
      cases u
      change Nonempty (Fin m)
      exact Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero NeZero.out)

def action (m : ℕ) : (i : Color) → Subgroup (Equiv.Perm (points m i))
  | .inl _ => ternaryRegularAction
  | .inr _ => ⊤

def multiplicity (c : ℕ) : Color → ℕ
  | .inl _ => c
  | .inr _ => 1

def tailIndex (c : ℕ) : Fin (multiplicity c (.inr PUnit.unit)) :=
  ⟨0, by simp [multiplicity]⟩

theorem fin_eq_tailIndex (c : ℕ)
    (j : Fin (multiplicity c (.inr PUnit.unit))) : j = tailIndex c := by
  apply Fin.ext
  simp [tailIndex]

abbrev ModelPoints (c m : ℕ) := OrbitProfilePoints (points m) (multiplicity c)
abbrev Product (c m : ℕ) := OrbitProfileProductGroup (multiplicity c) (action m)

def tailPermAt (c m : ℕ) (f : Product c m)
    (j : Fin (multiplicity c (.inr PUnit.unit))) : Equiv.Perm (Fin m) := by
  simpa only [action, points] using (f (.inr PUnit.unit) j).1

def tailPerm (c m : ℕ) (f : Product c m) : Equiv.Perm (Fin m) := by
  exact tailPermAt c m f (tailIndex c)

def tailNormalizerPermAt (c m : ℕ)
    (a : OrbitProfileCoordinates (points m) (multiplicity c) (action m)) :
    Fin (multiplicity c (.inr PUnit.unit)) → Equiv.Perm (Fin m) := fun j => by
  simpa only [action, points] using (a.2 (.inr PUnit.unit) j).1

def tailNormalizerPerm (c m : ℕ)
    (a : OrbitProfileCoordinates (points m) (multiplicity c) (action m)) :
    Equiv.Perm (Fin m) := by
  exact tailNormalizerPermAt c m a (tailIndex c)

/-- Literal identification of the profile product with an elementary
ternary top times the full permutation group of the merged tail. -/
def sourceEquiv (c m : ℕ) :
    Product c m ≃* (TernaryProductGraphBound.Elementary c × Equiv.Perm (Fin m)) where
  toFun f :=
    (Multiplicative.ofAdd (fun j =>
      (ternaryRegularEquiv.symm (f (.inl PUnit.unit) j)).toAdd),
      tailPerm c m f)
  invFun z i := by
    cases i with
    | inl u =>
        cases u
        exact fun j => ternaryRegularEquiv
          (Multiplicative.ofAdd (z.1.toAdd j))
    | inr u =>
        cases u
        exact fun _ => ⟨z.2, by simp [action]⟩
  left_inv f := by
    funext i
    cases i with
    | inl u =>
        cases u
        funext j
        exact ternaryRegularEquiv.apply_symm_apply _
    | inr u =>
        cases u
        funext j
        rw [fin_eq_tailIndex c j]
        apply Subtype.ext
        rfl
  right_inv z := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext j
      exact congrArg Multiplicative.toAdd
        (ternaryRegularEquiv.symm_apply_apply (Multiplicative.ofAdd (z.1.toAdd j)))
    · rfl
  map_mul' f g := by
    apply Prod.ext
    · apply Multiplicative.toAdd.injective
      funext j
      change (ternaryRegularEquiv.symm
          (f (.inl PUnit.unit) j * g (.inl PUnit.unit) j)).toAdd =
        (ternaryRegularEquiv.symm (f (.inl PUnit.unit) j)).toAdd +
          (ternaryRegularEquiv.symm (g (.inl PUnit.unit) j)).toAdd
      exact congrArg Multiplicative.toAdd
        (map_mul ternaryRegularEquiv.symm
          (f (.inl PUnit.unit) j) (g (.inl PUnit.unit) j))
    · rfl

def TailRankCapped (c d m : ℕ) (H : Subgroup (Product c m)) : Prop :=
  TernaryProductGraphBound.TailRankCapped c d
    (H.map (sourceEquiv c m).toMonoidHom)

/-- Permutation models obtained from a capped literal product subgroup. -/
def modelPredicate (c d m : ℕ)
    (K : Subgroup (Equiv.Perm (ModelPoints c m))) : Prop :=
  ∃ H : Subgroup (Product c m), TailRankCapped c d m H ∧
    H.map (orbitProfileProductAction (multiplicity c) (action m)) = K

private theorem sourceEquiv_coordinate_tail
    (c m : ℕ)
    (a : OrbitProfileCoordinates (points m) (multiplicity c) (action m))
    (x : Product c m) :
    (sourceEquiv c m (orbitProfileProductCoordinateEquiv a x)).2 =
      tailNormalizerPerm c m a *
        (sourceEquiv c m x).2 *
          (tailNormalizerPerm c m a)⁻¹ := by
  have hj : (a.1 (.inr PUnit.unit)).symm (tailIndex c) = tailIndex c :=
    fin_eq_tailIndex c _
  change tailPerm c m (orbitProfileProductCoordinateEquiv a x) = _
  change tailNormalizerPermAt c m a
      ((a.1 (.inr PUnit.unit)).symm (tailIndex c)) *
        tailPermAt c m x ((a.1 (.inr PUnit.unit)).symm (tailIndex c)) *
      (tailNormalizerPermAt c m a
        ((a.1 (.inr PUnit.unit)).symm (tailIndex c)))⁻¹ =
    tailNormalizerPerm c m a * tailPerm c m x *
      (tailNormalizerPerm c m a)⁻¹
  rw [hj]
  rfl

theorem tailRankCapped_coordinate
    (c d m : ℕ)
    (a : OrbitProfileCoordinates (points m) (multiplicity c) (action m))
    (H : Subgroup (Product c m)) (hH : TailRankCapped c d m H) :
    TailRankCapped c d m
      (H.map (orbitProfileProductCoordinateEquiv a).toMonoidHom) := by
  let t : Equiv.Perm (Fin m) := tailNormalizerPerm c m a
  have htail :
      ((H.map (orbitProfileProductCoordinateEquiv a).toMonoidHom).map
          (sourceEquiv c m).toMonoidHom).map
          (MonoidHom.snd (TernaryProductGraphBound.Elementary c)
            (Equiv.Perm (Fin m))) =
        ((H.map (sourceEquiv c m).toMonoidHom).map
          (MonoidHom.snd (TernaryProductGraphBound.Elementary c)
            (Equiv.Perm (Fin m)))).map (MulAut.conj t).toMonoidHom := by
    simp only [Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact sourceEquiv_coordinate_tail c m a x
  unfold TailRankCapped TernaryProductGraphBound.TailRankCapped at hH ⊢
  rw [TernaryProductGraphBound.tail_of_classification] at hH
  rw [TernaryProductGraphBound.tail_of_classification, htail]
  change ternaryCharacterRank _ ≤ d at hH ⊢
  rw [ternaryCharacterRank_map_conj]
  exact hH

/-- The capped model family is invariant under all original block
normalizers and permutations of the equal regular triples. -/
theorem modelPredicate_natural (c d m : ℕ) :
    OrbitProfileFamilyNatural (points m) (multiplicity c) (action m)
      (modelPredicate c d m) := by
  rintro w ⟨a, rfl⟩ K ⟨H,hcap,rfl⟩
  refine ⟨H.map (orbitProfileProductCoordinateEquiv a).toMonoidHom,
    tailRankCapped_coordinate c d m a H hcap, ?_⟩
  exact (relabel_productAction_map_coordinate a H).symm

/-- The model count is bounded by the restricted elementary-top graph
count; the actual tail subgroup is retained by the source equivalence. -/
theorem model_card_le (c d m : ℕ) :
    Nat.card {K : Subgroup (Equiv.Perm (ModelPoints c m)) //
        modelPredicate c d m K} ≤
      subgroupCount m *
        ((c + 1) * 3 ^ (c * c / 4 + c + d * c)) := by
  let Source := {H : Subgroup (Product c m) // TailRankCapped c d m H}
  let f : Source → {K : Subgroup (Equiv.Perm (ModelPoints c m)) //
      modelPredicate c d m K} := fun H =>
    ⟨H.1.map (orbitProfileProductAction (multiplicity c) (action m)),
      H.1, H.2, rfl⟩
  have hf : Function.Surjective f := by
    rintro ⟨K,H,hH,rfl⟩
    exact ⟨⟨H,hH⟩,rfl⟩
  have hfirst : Nat.card {K : Subgroup (Equiv.Perm (ModelPoints c m)) //
      modelPredicate c d m K} ≤ Nat.card Source :=
    Nat.card_le_card_of_surjective f hf
  let Target := {H : Subgroup
      (TernaryProductGraphBound.Elementary c × Equiv.Perm (Fin m)) //
        TernaryProductGraphBound.TailRankCapped c d H}
  let g : Source → Target := fun H =>
    ⟨H.1.map (sourceEquiv c m).toMonoidHom, H.2⟩
  have hg : Function.Injective g := by
    intro H K h
    apply Subtype.ext
    exact Subgroup.map_injective (sourceEquiv c m).injective
      (congrArg Subtype.val h)
  exact hfirst.trans ((Nat.card_le_card_of_injective g hg).trans
    (TernaryProductGraphBound.card_tailRankCapped_le c d))

/-- The exact original-action weight of a repeated regular-`C3` profile
with one nonempty merged tail.  The two denominator factors are literally
`6^c c!` and `m!`; no pointed-orbit multiplicity is charged. -/
theorem assembled_card_le (c d m : ℕ) (hm : 0 < m) {X : Type}
    (e : ModelPoints c m ≃ X) :
    (Nat.card (AssembledOrbitProfileOn (modelPredicate c d m) X) : ℝ) ≤
      (((3 * c + m).factorial : ℝ) *
          ((subgroupCount m : ℝ) *
            ((c + 1 : ℕ) * 3 ^ (c * c / 4 + c + d * c)))) /
        (((6 : ℝ) ^ c * (c.factorial : ℝ)) * (m.factorial : ℝ)) := by
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have hmodel :
      (Nat.card {K : Subgroup (Equiv.Perm (ModelPoints c m)) //
          modelPredicate c d m K} : ℝ) ≤
        (subgroupCount m : ℝ) *
          ((c + 1 : ℕ) * 3 ^ (c * c / 4 + c + d * c)) := by
    exact_mod_cast model_card_le c d m
  have h := assembledOrbitProfileOn_card_le_real_of_model_bound
    (modelPredicate_natural c d m) e hmodel
  have htail : Nat.card (Subgroup.normalizer
      ((⊤ : Subgroup (Equiv.Perm (Fin m))) : Set (Equiv.Perm (Fin m)))) =
        m.factorial := by
    rw [Subgroup.normalizer_eq_top]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  have hdegree :
      (∑ i, multiplicity c i * Fintype.card (points m i)) = 3 * c + m := by
    have hcard : Fintype.card TernaryCyclic = 3 := by
      norm_num [TernaryCyclic]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    change c * Fintype.card TernaryCyclic + 1 * Fintype.card (Fin m) = _
    rw [hcard, Fintype.card_fin]
    omega
  have hternaryF : Fintype.card (Subgroup.normalizer
      (ternaryRegularAction : Set (Equiv.Perm TernaryCyclic))) = 6 := by
    simpa only [Nat.card_eq_fintype_card] using
      ternaryRegularAction_normalizer_card
  have htailF : Fintype.card (Subgroup.normalizer
      ((⊤ : Subgroup (Equiv.Perm (Fin m))) : Set (Equiv.Perm (Fin m)))) =
        m.factorial := by
    simpa only [Nat.card_eq_fintype_card] using htail
  have hden :
      (∏ i, (Nat.card (Subgroup.normalizer
          (action m i : Set (Equiv.Perm (points m i)))) : ℝ) ^
            multiplicity c i * ((multiplicity c i).factorial : ℝ)) =
        ((6 : ℝ) ^ c * (c.factorial : ℝ)) * (m.factorial : ℝ) := by
    simp only [Fintype.prod_sum_type, Fintype.prod_unique]
    simp only [multiplicity, action, points, Nat.card_eq_fintype_card]
    change (Fintype.card (Subgroup.normalizer
        (ternaryRegularAction : Set (Equiv.Perm TernaryCyclic))) : ℝ) ^ c *
          (c.factorial : ℝ) *
        ((Fintype.card (Subgroup.normalizer
          ((⊤ : Subgroup (Equiv.Perm (Fin m))) : Set (Equiv.Perm (Fin m)))) : ℝ) ^ 1 *
            ((1 : ℕ).factorial : ℝ)) = _
    rw [hternaryF, htailF]
    norm_num
  rw [hdegree, hden] at h
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow] using h

end RepeatedC3TailProfile
end SymmetricSubgroupAsymptotics

end
