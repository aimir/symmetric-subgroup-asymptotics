import SymmetricSubgroupAsymptotics.OrbitProfileProductSum
import SymmetricSubgroupAsymptotics.BinaryCarrierCriticalOccurrence
import SymmetricSubgroupAsymptotics.BinaryCarrierWordProductEnergy
import SymmetricSubgroupAsymptotics.OrbitProfileUpperWeights

/-! Reusable original-action transport for any finite binary carrier menu.
The numerical inputs certify the exact occurrence word and bound its
original factor orders. They do not assume a subgroup count. All critical
and carrier coordinate fullness and arbitrary original survival predicates
are preserved before the fixed-word terminal theorem is applied once.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfile

open BinaryCarrierWord BinaryCarrierOccurrenceWord

variable {ι : Type} [Fintype ι] (Ω : ι → Type)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i))) (hU : ∀ i, IsPGroup 2 (U i))

/-- Store the literal original permutation subgroup, with its own action. -/
def localFactor (i : ι) : Factor where
  Carrier := U i
  group := inferInstance
  finite := inferInstance
  binary := hU i

def points : CriticalActionKind ⊕ ι → Type
  | .inl i => criticalActionPoints i
  | .inr i => Ω i

instance (i : CriticalActionKind ⊕ ι) : Fintype (points Ω i) := by
  cases i <;> dsimp [points] <;> infer_instance

instance (i : CriticalActionKind ⊕ ι) : Nonempty (points Ω i) := by
  cases i <;> dsimp [points] <;> infer_instance

def action : (i : CriticalActionKind ⊕ ι) → Subgroup (Equiv.Perm (points Ω i))
  | .inl i => criticalActionSubgroup i
  | .inr i => U i

variable (p : CriticalProfile) (m : ι → ℕ)

def multiplicity : CriticalActionKind ⊕ ι → ℕ := Sum.elim p.multiplicity m

abbrev ModelPoints := OrbitProfilePoints (points Ω) (multiplicity p m)

abbrev ModelFamily (P : Subgroup (Equiv.Perm (ModelPoints Ω p m)) → Prop) :=
  {K : Subgroup (Equiv.Perm (ModelPoints Ω p m)) //
    OrbitProfileFull (action Ω U) 1 K ∧ P K}

abbrev OriginalProduct := OrbitProfileProductGroup (multiplicity p m) (action Ω U)

/-- Faithfulness and the original maps condition give exact reconstruction
of the complete permutation subgroup, including its arbitrary predicate. -/
def modelEquivProduct (P : Subgroup (Equiv.Perm (ModelPoints Ω p m)) → Prop) :
    ModelFamily Ω U p m P ≃
      {H : Subgroup (OriginalProduct Ω U p m) //
        OrbitProfileProductFull (multiplicity p m) (action Ω U) H ∧
          P (H.map (orbitProfileProductAction (multiplicity p m) (action Ω U)))} where
  toFun K := ⟨K.1.comap (orbitProfileProductAction (multiplicity p m) (action Ω U)),
    orbitProfileFull_comap K.2.1,by
      rw [Subgroup.map_comap_eq_self (orbitProfileFull_le_product_range K.2.1)]
      exact K.2.2⟩
  invFun H := ⟨H.1.map (orbitProfileProductAction (multiplicity p m) (action Ω U)),
    orbitProfileProductFull_map H.2.1,H.2.2⟩
  left_inv K := by
    apply Subtype.ext
    exact Subgroup.map_comap_eq_self (orbitProfileFull_le_product_range K.2.1)
  right_inv H := by
    apply Subtype.ext
    exact Subgroup.comap_map_eq_self_of_injective
      (orbitProfileProductAction_injective (multiplicity p m) (action Ω U)) H.1

def decodeSplit
    (H : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct p (localFactor Ω U hU) m)) :
    Subgroup (Equiv.Perm (ModelPoints Ω p m)) :=
  (H.comap (OrbitProfileProductSum.equiv (multiplicity p m) (action Ω U)).toMonoidHom).map
    (orbitProfileProductAction (multiplicity p m) (action Ω U))

def modelEquivSplit (P : Subgroup (Equiv.Perm (ModelPoints Ω p m)) → Prop) :
    ModelFamily Ω U p m P ≃
      BinaryCarrierCriticalOccurrence.OriginalFamily p (localFactor Ω U hU) m
        (fun H => P (decodeSplit Ω U hU p m H)) :=
  (modelEquivProduct Ω U p m P).trans
    (OrbitProfileProductSum.familyEquiv (multiplicity p m) (action Ω U)
      (fun H => P (H.map (orbitProfileProductAction (multiplicity p m) (action Ω U)))))

variable {L : ℕ} (occurrences : Fin L ≃ (Σ i, Fin (m i)))

abbrev TerminalGroup :=
  BinaryCarrierCriticalOccurrence.TerminalProduct p (localFactor Ω U hU) m occurrences

def terminalPredicate (P : Subgroup (Equiv.Perm (ModelPoints Ω p m)) → Prop) :=
  BinaryCarrierCriticalOccurrence.terminalPredicate p (localFactor Ω U hU) m occurrences
    (fun H => P (decodeSplit Ω U hU p m H))

def decodeTerminal (J : Subgroup (TerminalGroup Ω U hU p m occurrences)) :
    Subgroup (Equiv.Perm (ModelPoints Ω p m)) :=
  decodeSplit Ω U hU p m
    (BinaryCarrierCriticalOccurrence.decode p (localFactor Ω U hU) m occurrences J)

/-- Individual original fullness is retained; neither whole class-product
projection is required to be onto. Regular C2/V4 blocks stay in the predicate. -/
def modelEquivTerminal (P : Subgroup (Equiv.Perm (ModelPoints Ω p m)) → Prop) :
    ModelFamily Ω U p m P ≃
      TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
        (occurrenceWord (localFactor Ω U hU) m occurrences)
          (terminalPredicate Ω U hU p m occurrences P) :=
  (modelEquivSplit Ω U hU p m P).trans
    (BinaryCarrierCriticalOccurrence.originalFamilyEquivTerminal
      p (localFactor Ω U hU) m occurrences (fun H => P (decodeSplit Ω U hU p m H)))

theorem modelEquivTerminal_reconstruct
    (P : Subgroup (Equiv.Perm (ModelPoints Ω p m)) → Prop) (K : ModelFamily Ω U p m P) :
    decodeTerminal Ω U hU p m occurrences
        (modelEquivTerminal Ω U hU p m occurrences P K).1 = K.1 := by
  change ((modelEquivTerminal Ω U hU p m occurrences P).symm
    (modelEquivTerminal Ω U hU p m occurrences P K)).1 = K.1
  exact congrArg Subtype.val
    ((modelEquivTerminal Ω U hU p m occurrences P).symm_apply_apply K)

theorem modelFamily_card (P : Subgroup (Equiv.Perm (ModelPoints Ω p m)) → Prop) :
    Nat.card (ModelFamily Ω U p m P) =
      Nat.card (TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
        (occurrenceWord (localFactor Ω U hU) m occurrences)
          (terminalPredicate Ω U hU p m occurrences P)) :=
  Nat.card_congr (modelEquivTerminal Ω U hU p m occurrences P)

/-- The only numerical inputs are a certificate on the exact original
normal histories and an order bound for their original factors. -/
theorem modelFamily_card_le_reserve (b : ℕ)
    (hb : OrderBound (occurrenceWord (localFactor Ω U hU) m occurrences) b)
    (T : ℝ) (cert : CertifiedHistoryRows (occurrenceWord (localFactor Ω U hU) m occurrences) T)
    (P : Subgroup (Equiv.Perm (ModelPoints Ω p m)) → Prop) :
    (Nat.card (ModelFamily Ω U p m P) : ℝ) ≤
      terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p) b L T := by
  rw [modelFamily_card Ω U hU p m occurrences P]
  simpa only [occurrenceWord_length] using
    terminal_product_subgroups_le_reserve_of_orderBound p.abelianRank
      (criticalProfileNonabelianChoice p) (occurrenceWord (localFactor Ω U hU) m occurrences)
      b hb T cert (terminalPredicate Ω U hU p m occurrences P)

/-- Physical degree is the original sum of block sizes, independently of
the certificate scale T and the number L of carrier positions. -/
def physicalDegree : ℕ :=
  ∑ i, multiplicity p m i * Fintype.card (points Ω i)

def originalDenominator : ℝ :=
  ∏ i, (Nat.card (Subgroup.normalizer
    (action Ω U i : Set (Equiv.Perm (points Ω i)))) : ℝ) ^ multiplicity p m i *
      (multiplicity p m i).factorial

/-- Apply the original normalizer and occurrence-factorial denominator
to the whole full family. No model-count or naturality hypothesis is added. -/
theorem full_profile_card_le_reserve (b : ℕ)
    (hb : OrderBound (occurrenceWord (localFactor Ω U hU) m occurrences) b)
    (T : ℝ) (cert : CertifiedHistoryRows (occurrenceWord (localFactor Ω U hU) m occurrences) T)
    {X : Type*} (labels : ModelPoints Ω p m ≃ X) :
    (Nat.card (FullOrbitProfileOn (points Ω) (multiplicity p m) (action Ω U) X) : ℝ) ≤
      ((physicalDegree Ω p m).factorial : ℝ) *
        terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p) b L T /
          originalDenominator Ω U p m := by
  rw [← Nat.card_congr (assembledFullOrbitProfileEquiv
    (X := X) (m := multiplicity p m) (action Ω U))]
  have hmodel :
      (Nat.card {K // OrbitProfileFull (m := multiplicity p m) (action Ω U) 1 K} : ℝ) ≤
        terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p) b L T := by
    simpa only [ModelFamily, and_true] using
      modelFamily_card_le_reserve Ω U hU p m occurrences b hb T cert (fun _ => True)
  simpa only [physicalDegree, originalDenominator] using
    assembledOrbitProfileOn_card_le_real_of_model_bound
      (orbitProfileFull_family_natural (multiplicity p m) (action Ω U)) labels hmodel

end SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfile
