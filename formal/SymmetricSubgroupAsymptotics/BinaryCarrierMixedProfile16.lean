import SymmetricSubgroupAsymptotics.OrbitProfileProductSum
import SymmetricSubgroupAsymptotics.BinaryCarrierCriticalOccurrence
import SymmetricSubgroupAsymptotics.BinaryCarrierMasterProduct16

/-! The literal mixed critical/master model family satisfies the checked
degree-sixteen word reserve. All original occurrence projections and an
arbitrary predicate on the complete original permutation subgroup survive
the faithful product action, sum regrouping and terminal coordinate chart.
No replacement action or normalizer enters this transport.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfile16

open BinaryCarrierWord BinaryCarrierOccurrenceWord BinaryCarrierMasterWords16

/-- The five original degree-sixteen permutation closures. -/
def masterAction : Master → Subgroup (Equiv.Perm (Fin 16))
  | .t1082 => BinaryCarrierDerivedOrder16T1082.Original
  | .t1083 => BinaryCarrierDerivedOrder16T1083.Original
  | .t1084 => BinaryCarrierDerivedOrder16T1084.Original
  | .t1332 => BinaryCarrierDerivedOrder16T1332.Original
  | .t1547 => BinaryCarrierDerivedOrder16T1547.Original

def localFactor (i : Master) : Factor where
  Carrier := masterAction i
  group := inferInstance
  finite := inferInstance
  binary := by
    cases i with
    | t1082 => exact BinaryCarrierExactOrder16T1082.original_isPGroup
    | t1083 => exact BinaryCarrierExactOrder16T1083.original_isPGroup
    | t1084 => exact BinaryCarrierExactOrder16T1084.original_isPGroup
    | t1332 => exact BinaryCarrierExactOrder16T1332.original_isPGroup
    | t1547 => exact BinaryCarrierExactOrder16T1547.original_isPGroup

/-- The factor structure is the already checked literal master structure. -/
theorem localFactor_eq (i : Master) : localFactor i = factor i := by
  cases i <;> rfl

abbrev Kind := CriticalActionKind ⊕ Master

def points : Kind → Type
  | .inl i => criticalActionPoints i
  | .inr _ => Fin 16

instance (i : Kind) : Fintype (points i) := by
  cases i <;> dsimp [points] <;> infer_instance

instance (i : Kind) : Nonempty (points i) := by
  cases i <;> dsimp [points] <;> infer_instance

def action : (i : Kind) → Subgroup (Equiv.Perm (points i))
  | .inl i => criticalActionSubgroup i
  | .inr i => masterAction i

variable (p : CriticalProfile) (m : Master → ℕ)

def multiplicity : Kind → ℕ := Sum.elim p.multiplicity m

abbrev ModelPoints := OrbitProfilePoints points (multiplicity p m)

abbrev ModelFamily (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) :=
  {K : Subgroup (Equiv.Perm (ModelPoints p m)) //
    OrbitProfileFull action 1 K ∧ P K}

abbrev OriginalProduct := OrbitProfileProductGroup (multiplicity p m) action

/-- Pull back by the original faithful block action, retaining P on its
literal permutation image. Fullness supplies the exact range containment. -/
def modelEquivProduct (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) :
    ModelFamily p m P ≃
      {H : Subgroup (OriginalProduct p m) //
        OrbitProfileProductFull (multiplicity p m) action H ∧
          P (H.map (orbitProfileProductAction (multiplicity p m) action))} where
  toFun K := ⟨K.1.comap (orbitProfileProductAction (multiplicity p m) action),
    orbitProfileFull_comap K.2.1,by
      rw [Subgroup.map_comap_eq_self (orbitProfileFull_le_product_range K.2.1)]
      exact K.2.2⟩
  invFun H := ⟨H.1.map (orbitProfileProductAction (multiplicity p m) action),
    orbitProfileProductFull_map H.2.1,H.2.2⟩
  left_inv K := by
    apply Subtype.ext
    exact Subgroup.map_comap_eq_self (orbitProfileFull_le_product_range K.2.1)
  right_inv H := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective
      (orbitProfileProductAction_injective (multiplicity p m) action) H.1

/-- Reconstruct the actual permutation subgroup from the two original
occurrence products, before the terminal coordinates are chosen. -/
def decodeSplit
    (L : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct p localFactor m)) :
    Subgroup (Equiv.Perm (ModelPoints p m)) :=
  (L.comap (OrbitProfileProductSum.equiv (multiplicity p m) action).toMonoidHom).map
    (orbitProfileProductAction (multiplicity p m) action)

def modelEquivSplit (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) :
    ModelFamily p m P ≃
      BinaryCarrierCriticalOccurrence.OriginalFamily p localFactor m
        (fun L => P (decodeSplit p m L)) :=
  (modelEquivProduct p m P).trans
    (OrbitProfileProductSum.familyEquiv (multiplicity p m) action
      (fun H => P (H.map (orbitProfileProductAction (multiplicity p m) action))))

variable {n : ℕ} (e : Fin n ≃ (Σ i, Fin (m i)))

abbrev TerminalGroup :=
  BinaryCarrierCriticalOccurrence.TerminalProduct p localFactor m e

def terminalPredicate (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) :=
  BinaryCarrierCriticalOccurrence.terminalPredicate p localFactor m e
    (fun L => P (decodeSplit p m L))

/-- This is the literal original permutation subgroup, not a selected
isomorphism type, normal history or envelope label. -/
def decodeTerminal (J : Subgroup (TerminalGroup p m e)) :
    Subgroup (Equiv.Perm (ModelPoints p m)) :=
  decodeSplit p m (BinaryCarrierCriticalOccurrence.decode p localFactor m e J)

def modelEquivTerminal (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) :
    ModelFamily p m P ≃
      TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
        (occurrenceWord localFactor m e) (terminalPredicate p m e P) :=
  (modelEquivSplit p m P).trans
    (BinaryCarrierCriticalOccurrence.originalFamilyEquivTerminal p localFactor m e
      (fun L => P (decodeSplit p m L)))

theorem modelEquivTerminal_reconstruct
    (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) (K : ModelFamily p m P) :
    decodeTerminal p m e (modelEquivTerminal p m e P K).1 = K.1 := by
  change ((modelEquivTerminal p m e P).symm (modelEquivTerminal p m e P K)).1 = K.1
  exact congrArg Subtype.val ((modelEquivTerminal p m e P).symm_apply_apply K)

theorem modelFamily_card (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) :
    Nat.card (ModelFamily p m P) =
      Nat.card (TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
        (occurrenceWord localFactor m e) (terminalPredicate p m e P)) :=
  Nat.card_congr (modelEquivTerminal p m e P)

/-- The same enumeration, with one original master at every position. -/
def selectedMasters : List Master := List.ofFn (fun j => (e j).1)

theorem selectedMasters_word :
    word (selectedMasters m e) = occurrenceWord localFactor m e := by
  simp only [word, selectedMasters, occurrenceWord, List.map_ofFn, Function.comp_def,
    localFactor_eq]

/-- The checked terminal reserve, with original critical rank and the
number of original degree-sixteen occurrences. -/
def reserve (L : ℕ) : ℝ :=
  (((binaryStructuredOrderConstant 12 *
    (12*L+2)^(binaryStructuredOrderConstant 12) : ℕ) : ℝ)^L) *
    (((eulerProduct⁻¹)^3 * ((p.rank+1 : ℕ) : ℝ) *
      (∑ ell ∈ Finset.range (p.d8+p.e8+1), (72 : ℝ)^ell)) *
        ((2 : ℝ)^(4096*L) *
          (2 : ℝ)^(((p.rank : ℝ)+4*(2*(L : ℝ)))^2/4 -
            (25/82)*p.rank*(2*(L : ℝ)) - (29/164)*(2*(L : ℝ))^2)))

private theorem terminal_card_le_reserve_of_word
    (masters : List Master) (w : List Factor) (hw : word masters = w)
    (P : Subgroup (CriticalProfileCoordinateGroup p × Product w) → Prop) :
    (Nat.card (TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
      w P) : ℝ) ≤ reserve p masters.length := by
  subst w
  simpa only [reserve, criticalProfile_product_rank, CriticalProfileNonabelianIndex,
    Fintype.card_sum, Fintype.card_fin] using
    terminal_product_subgroups_le_reserve p.abelianRank
      (criticalProfileNonabelianChoice p) masters P

include e in
/-- Unconditional model count for these literal mixed actions. P remains
arbitrary, including complete survival and earlier-owner exclusions. The
original physical profile normalizer multiplier is applied separately. -/
theorem modelFamily_card_le_reserve
    (P : Subgroup (Equiv.Perm (ModelPoints p m)) → Prop) :
    (Nat.card (ModelFamily p m P) : ℝ) ≤ reserve p n := by
  rw [modelFamily_card p m e P]
  have h := terminal_card_le_reserve_of_word p (selectedMasters m e)
    (occurrenceWord localFactor m e) (selectedMasters_word m e) (terminalPredicate p m e P)
  simpa only [selectedMasters, List.length_ofFn] using h

end SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfile16
