import SymmetricSubgroupAsymptotics.OddMarker
import SymmetricSubgroupAsymptotics.CriticalProfileAssembly

/-!
# Original actions and weights for the two odd critical markers

The singleton and natural S3 marker have different actual orbit profiles.
Their original normalizer weights are respectively one and one sixth.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

inductive OddCriticalActionKind
  | fixed | marker | binary (i : CriticalActionKind)
  deriving DecidableEq, Fintype

def oddCriticalActionPoints : OddCriticalActionKind → Type
  | .fixed => Fin 1
  | .marker => Fin 3
  | .binary i => criticalActionPoints i

instance (i : OddCriticalActionKind) : Fintype (oddCriticalActionPoints i) := by
  cases i <;> dsimp [oddCriticalActionPoints] <;> infer_instance

instance (i : OddCriticalActionKind) : Nonempty (oddCriticalActionPoints i) := by
  cases i <;> dsimp [oddCriticalActionPoints] <;> infer_instance

instance (i : OddCriticalActionKind) : DecidableEq (oddCriticalActionPoints i) := by
  cases i <;> dsimp [oddCriticalActionPoints] <;> infer_instance

def oddCriticalActionSubgroup :
    (i : OddCriticalActionKind) → Subgroup (Equiv.Perm (oddCriticalActionPoints i))
  | .fixed => ⊤
  | .marker => oddMarkerActionSubgroup
  | .binary i => criticalActionSubgroup i

def oddCriticalActionOrder : OddCriticalActionKind → ℕ
  | .fixed => 1
  | .marker => 6
  | .binary i => criticalActionOrder i

def oddCriticalActionNormalizerOrder : OddCriticalActionKind → ℕ
  | .fixed => 1
  | .marker => 6
  | .binary i => criticalActionNormalizerOrder i

theorem oddCriticalAction_point_card (i : OddCriticalActionKind) :
    Fintype.card (oddCriticalActionPoints i) =
      match i with | .fixed => 1 | .marker => 3 | .binary j => criticalActionDegree j := by
  cases i with
  | fixed => change Fintype.card (Fin 1) = 1; norm_num
  | marker => change Fintype.card (Fin 3) = 3; norm_num
  | binary j => exact criticalAction_point_card j

theorem oddCriticalAction_group_card (i : OddCriticalActionKind) :
    Nat.card (oddCriticalActionSubgroup i) = oddCriticalActionOrder i := by
  cases i with
  | fixed =>
    change Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 1))) = 1
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  | marker =>
    change Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 3))) = 6
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  | binary i => exact criticalAction_group_card i

theorem oddCriticalAction_normalizer_card (i : OddCriticalActionKind) :
    Nat.card (Subgroup.normalizer
      (oddCriticalActionSubgroup i : Set (Equiv.Perm (oddCriticalActionPoints i)))) =
      oddCriticalActionNormalizerOrder i := by
  cases i with
  | fixed =>
    have h : Subgroup.normalizer (oddCriticalActionSubgroup .fixed :
        Set (Equiv.Perm (oddCriticalActionPoints .fixed))) = ⊤ := by
      ext g
      change (∀ h : Equiv.Perm (oddCriticalActionPoints .fixed), h ∈ Set.univ ↔
        g * h * g⁻¹ ∈ Set.univ) ↔ True
      simp
    rw [h]
    change Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 1))) = 1
    rw [Nat.card_congr (Subgroup.topEquiv).toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]
  | marker => exact oddMarker_normalizer_card
  | binary i => exact criticalAction_normalizer_card i

theorem oddCriticalAction_transitive (i : OddCriticalActionKind)
    (x y : oddCriticalActionPoints i) :
    ∃ g : oddCriticalActionSubgroup i,
      (g : Equiv.Perm (oddCriticalActionPoints i)) x = y := by
  cases i with
  | fixed =>
    refine ⟨1, ?_⟩
    change x = y
    exact @Subsingleton.elim (Fin 1) _ x y
  | marker => exact oddMarker_transitive x y
  | binary i => exact criticalAction_transitive i x y

/-- The six actual action groups have distinct orders, including the two
binary colours with four physical points. -/
theorem oddCriticalAction_types_separated :
    OrbitActionTypesSeparated oddCriticalActionPoints oddCriticalActionSubgroup := by
  intro i j e hij hji
  have hle : Nat.card (oddCriticalActionSubgroup i) ≤ Nat.card (oddCriticalActionSubgroup j) := by
    apply Nat.card_le_card_of_injective
      (fun u : oddCriticalActionSubgroup i ↦
        (⟨e.permCongr u.1, hij u.1 u.2⟩ : oddCriticalActionSubgroup j))
    intro u v h
    exact Subtype.ext (e.permCongr.injective (congrArg Subtype.val h))
  have hge : Nat.card (oddCriticalActionSubgroup j) ≤ Nat.card (oddCriticalActionSubgroup i) := by
    apply Nat.card_le_card_of_injective
      (fun u : oddCriticalActionSubgroup j ↦
        (⟨e.symm.permCongr u.1, hji u.1 u.2⟩ : oddCriticalActionSubgroup i))
    intro u v h
    exact Subtype.ext (e.symm.permCongr.injective (congrArg Subtype.val h))
  have hinj : Function.Injective oddCriticalActionOrder := by decide
  apply hinj
  rw [← oddCriticalAction_group_card i, ← oddCriticalAction_group_card j]
  exact Nat.le_antisymm hle hge

/-- False selects the singleton; true selects the original natural S3. -/
def oddCriticalMultiplicity (marker : Bool) (p : CriticalProfile) : OddCriticalActionKind → ℕ
  | .fixed => if marker then 0 else 1
  | .marker => if marker then 1 else 0
  | .binary i => p.multiplicity i

private theorem oddCriticalActionKind_univ : (Finset.univ : Finset OddCriticalActionKind) =
    {.fixed, .marker, .binary .c2, .binary .v4, .binary .d8, .binary .e8} := by decide

theorem oddCriticalMultiplicity_degree (marker : Bool) (p : CriticalProfile) :
    ∑ i, oddCriticalMultiplicity marker p i * Fintype.card (oddCriticalActionPoints i) =
      2 * p.rank + (if marker then 3 else 1) := by
  rw [oddCriticalActionKind_univ]
  cases marker <;>
    simp [oddCriticalMultiplicity, oddCriticalAction_point_card,
      criticalActionDegree, CriticalProfile.multiplicity, CriticalProfile.rank] <;> omega

theorem oddCriticalMultiplicity_weight (marker : Bool) (p : CriticalProfile) :
    (∏ i, (Nat.card (Subgroup.normalizer (oddCriticalActionSubgroup i :
      Set (Equiv.Perm (oddCriticalActionPoints i)))) : ℚ) ^ oddCriticalMultiplicity marker p i *
        (oddCriticalMultiplicity marker p i).factorial)⁻¹ =
      p.weight / (if marker then 6 else 1) := by
  simp only [oddCriticalAction_normalizer_card, oddCriticalActionKind_univ]
  cases marker <;>
    simp [oddCriticalActionNormalizerOrder, oddCriticalMultiplicity,
      criticalActionNormalizerOrder, CriticalProfile.multiplicity,
      CriticalProfile.weight, one_div, mul_assoc]
  ring

theorem oddCriticalMultiplicity_injective :
    Function.Injective (fun q : Bool × CriticalProfile ↦ oddCriticalMultiplicity q.1 q.2) := by
  rintro ⟨b,p⟩ ⟨c,q⟩ h
  have hb := congrFun h OddCriticalActionKind.marker
  have hbc : b = c := by cases b <;> cases c <;> simp_all [oddCriticalMultiplicity]
  subst c
  have hp : p = q := by
    apply CriticalProfile.multiplicity_injective
    funext i
    exact congrFun h (.binary i)
  subst q
  rfl

/-- Literal full model subgroups on the six original action types. -/
abbrev OddCriticalModelSubgroups (marker : Bool) (p : CriticalProfile) :=
  {H : Subgroup (Equiv.Perm (OrbitProfilePoints oddCriticalActionPoints
      (oddCriticalMultiplicity marker p))) // OrbitProfileFull oddCriticalActionSubgroup 1 H}

abbrev OddCriticalProfileSubgroups (marker : Bool) (p : CriticalProfile) :=
  FullOrbitProfileOn oddCriticalActionPoints (oddCriticalMultiplicity marker p)
    oddCriticalActionSubgroup (Fin (2 * p.rank + (if marker then 3 else 1)))

/-- Both marker choices keep their original labelling and normalizer weight. -/
theorem oddCriticalProfileSubgroups_card (marker : Bool) (p : CriticalProfile) :
    (Nat.card (OddCriticalProfileSubgroups marker p) : ℚ) =
      ((2 * p.rank + (if marker then 3 else 1)).factorial : ℚ) *
        (p.weight / (if marker then 6 else 1)) * Nat.card (OddCriticalModelSubgroups marker p) := by
  have h := fullOrbitProfileOn_fin_card_rat (oddCriticalMultiplicity marker p)
    oddCriticalActionSubgroup _ (oddCriticalMultiplicity_degree marker p)
    oddCriticalAction_transitive oddCriticalAction_types_separated
  change _ = _ at h
  rw [h, div_eq_mul_inv, oddCriticalMultiplicity_weight]
  ring

end SymmetricSubgroupAsymptotics
