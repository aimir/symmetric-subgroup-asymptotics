import SymmetricSubgroupAsymptotics.BinaryCarrierOccurrenceWord
import SymmetricSubgroupAsymptotics.BinaryCarrierTerminalFamily
import SymmetricSubgroupAsymptotics.CriticalProductTransport

/-! Regroup original critical and carrier occurrences into one terminal
product. Every original coordinate remains full, including each regular
C2 and V4 occurrence. The entire critical product need not be full.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierCriticalOccurrence

open BinaryCarrierWord BinaryCarrierOccurrenceWord

variable (p : CriticalProfile) {ι : Type} (F : ι → Factor) (m : ι → ℕ)
    {n : ℕ} (e : Fin n ≃ (Σ i, Fin (m i)))

abbrev OriginalProduct :=
  OrbitProfileProductGroup p.multiplicity criticalActionSubgroup × OccurrenceProduct F m

abbrev TerminalProduct :=
  CriticalProfileCoordinateGroup p × Product (occurrenceWord F m e)

/-- The critical chart preserves the original regular blocks through its
inverse. The carrier chart uses the specified enumeration of occurrences. -/
def productEquiv : OriginalProduct p F m ≃* TerminalProduct p F m e :=
  (criticalProfileProductEquiv p).prodCongr (occurrenceEquiv F m e).symm

/-- Fullness is tested on each original critical and carrier occurrence,
not on the projection to either entire product. -/
def OriginalFull (K : Subgroup (OriginalProduct p F m)) : Prop :=
  OrbitProfileProductFull p.multiplicity criticalActionSubgroup
      (K.map (MonoidHom.fst _ _)) ∧
    OccurrenceFull F m (K.map (MonoidHom.snd _ _))

abbrev OriginalFamily (P : Subgroup (OriginalProduct p F m) → Prop) :=
  {K : Subgroup (OriginalProduct p F m) // OriginalFull p F m K ∧ P K}

/-- The actual original subgroup, recovered through the inverse chart. -/
def decode (J : Subgroup (TerminalProduct p F m e)) :
    Subgroup (OriginalProduct p F m) :=
  J.comap (productEquiv p F m e).toMonoidHom

theorem decode_eq_inverse_map (J : Subgroup (TerminalProduct p F m e)) :
    decode p F m e J = J.map (productEquiv p F m e).symm.toMonoidHom :=
  Subgroup.comap_equiv_eq_map_symm' (productEquiv p F m e) J

theorem decode_map (K : Subgroup (OriginalProduct p F m)) :
    decode p F m e (K.map (productEquiv p F m e).toMonoidHom) = K :=
  Subgroup.comap_map_eq_self_of_injective (productEquiv p F m e).injective K

theorem map_decode (J : Subgroup (TerminalProduct p F m e)) :
    (decode p F m e J).map (productEquiv p F m e).toMonoidHom = J :=
  Subgroup.map_comap_eq_self_of_surjective (productEquiv p F m e).surjective J

theorem map_fst (K : Subgroup (OriginalProduct p F m)) :
    (K.map (productEquiv p F m e).toMonoidHom).map (MonoidHom.fst _ _) =
      (K.map (MonoidHom.fst _ _)).map (criticalProfileProductEquiv p).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem map_snd (K : Subgroup (OriginalProduct p F m)) :
    (K.map (productEquiv p F m e).toMonoidHom).map (MonoidHom.snd _ _) =
      (K.map (MonoidHom.snd _ _)).map (occurrenceEquiv F m e).symm.toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

theorem criticalFull_map_iff (K : Subgroup (OriginalProduct p F m)) :
    CriticalProfileCoordinateFull p
        ((K.map (productEquiv p F m e).toMonoidHom).map (MonoidHom.fst _ _)) ↔
      OrbitProfileProductFull p.multiplicity criticalActionSubgroup
        (K.map (MonoidHom.fst _ _)) := by
  rw [map_fst]
  unfold CriticalProfileCoordinateFull
  rw [Subgroup.comap_map_eq_self_of_injective
    (f := (criticalProfileProductEquiv p).toMonoidHom)
    (criticalProfileProductEquiv p).injective]

theorem tailFull_map_iff (K : Subgroup (OriginalProduct p F m)) :
    Full (occurrenceWord F m e)
        (SubdirectTailImage.tail (K.map (productEquiv p F m e).toMonoidHom)) ↔
      OccurrenceFull F m (K.map (MonoidHom.snd _ _)) := by
  change Full (occurrenceWord F m e)
    ((K.map (productEquiv p F m e).toMonoidHom).map (MonoidHom.snd _ _)) ↔ _
  rw [map_snd]
  let L := K.map (MonoidHom.snd
    (OrbitProfileProductGroup p.multiplicity criticalActionSubgroup) (OccurrenceProduct F m))
  have he : (L.map (occurrenceEquiv F m e).symm.toMonoidHom).map
      (occurrenceEquiv F m e).toMonoidHom = L := by
    rw [Subgroup.map_equiv_eq_comap_symm' (occurrenceEquiv F m e).symm L]
    exact Subgroup.map_comap_eq_self_of_surjective
      (occurrenceEquiv F m e).surjective L
  have h := occurrenceFull_map_iff F m e
    (L.map (occurrenceEquiv F m e).symm.toMonoidHom)
  rw [he] at h
  exact h.symm

/-- Retain the complete original regular-block condition and test P on
the exact inverse subgroup. No invariance or factorization of P is required. -/
def terminalPredicate (P : Subgroup (OriginalProduct p F m) → Prop)
    (J : Subgroup (TerminalProduct p F m e)) : Prop :=
  CriticalProfileCoordinateFull p (J.map (MonoidHom.fst _ _)) ∧
    P (decode p F m e J)

def toTerminal (P : Subgroup (OriginalProduct p F m) → Prop)
    (K : OriginalFamily p F m P) :
    TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
      (occurrenceWord F m e) (terminalPredicate p F m e P) := by
  have hc := (criticalFull_map_iff p F m e K.1).mpr K.2.1.1
  refine ⟨K.1.map (productEquiv p F m e).toMonoidHom,
    (tailFull_map_iff p F m e K.1).mpr K.2.1.2, ?_, hc, ?_⟩
  · intro i
    have h := criticalProfileCoordinateFull_nonabelian p _ hc i
    simpa only [Subgroup.map_map] using h
  · rw [decode_map]
    exact K.2.2

def fromTerminal (P : Subgroup (OriginalProduct p F m) → Prop)
    (J : TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
      (occurrenceWord F m e) (terminalPredicate p F m e P)) :
    OriginalFamily p F m P := by
  refine ⟨decode p F m e J.1, ⟨?_, ?_⟩, J.2.2.2.2⟩
  · apply (criticalFull_map_iff p F m e (decode p F m e J.1)).mp
    rw [map_decode]
    exact J.2.2.2.1
  · apply (tailFull_map_iff p F m e (decode p F m e J.1)).mp
    rw [map_decode]
    exact J.2.1

/-- Exact family transport, including repeated factors, empty occurrence
sets and arbitrary predicates on the complete original subgroup. -/
def originalFamilyEquivTerminal (P : Subgroup (OriginalProduct p F m) → Prop) :
    OriginalFamily p F m P ≃
      TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
        (occurrenceWord F m e) (terminalPredicate p F m e P) where
  toFun := toTerminal p F m e P
  invFun := fromTerminal p F m e P
  left_inv K := by
    apply Subtype.ext
    exact decode_map p F m e K.1
  right_inv J := by
    apply Subtype.ext
    exact map_decode p F m e J.1

theorem toTerminal_injective (P : Subgroup (OriginalProduct p F m) → Prop) :
    Function.Injective (toTerminal p F m e P) :=
  (originalFamilyEquivTerminal p F m e P).injective

/-- The inverse returns the literal original subgroup, so every original
survival condition and any weight evaluated on it are preserved. -/
theorem toTerminal_reconstruct (P : Subgroup (OriginalProduct p F m) → Prop)
    (K : OriginalFamily p F m P) :
    decode p F m e (toTerminal p F m e P K).1 = K.1 :=
  decode_map p F m e K.1

theorem originalFamily_card (P : Subgroup (OriginalProduct p F m) → Prop) :
    Nat.card (OriginalFamily p F m P) =
      Nat.card (TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
        (occurrenceWord F m e) (terminalPredicate p F m e P)) :=
  Nat.card_congr (originalFamilyEquivTerminal p F m e P)

theorem originalFamily_card_le (P : Subgroup (OriginalProduct p F m) → Prop) :
    Nat.card (OriginalFamily p F m P) ≤
      Nat.card (TerminalProductFamily p.abelianRank (criticalProfileNonabelianChoice p)
        (occurrenceWord F m e) (terminalPredicate p F m e P)) :=
  (originalFamily_card p F m e P).le

end SymmetricSubgroupAsymptotics.BinaryCarrierCriticalOccurrence
