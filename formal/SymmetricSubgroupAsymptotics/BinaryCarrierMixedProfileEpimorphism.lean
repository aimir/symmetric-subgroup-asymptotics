import SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfile
import SymmetricSubgroupAsymptotics.CarrierEpimorphismPullback

/-! Original mixed profiles may be counted through fixed epimorphisms from
certified carrier masters. The exterior is the complete original critical
occurrence product, whose image may be proper. Each original occurrence
is lifted separately. Numerical certificates concern the source word;
physical points, normalizers and multiplicity factorials concern only the
original target actions. No equality of those physical weights is assumed.
-/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfileEpimorphism

open BinaryCarrierWord BinaryCarrierOccurrenceWord

abbrev CriticalOriginal (p : CriticalProfile) :=
  OrbitProfileProductGroup p.multiplicity criticalActionSubgroup

def criticalFull (p : CriticalProfile) (H : Subgroup (CriticalOriginal p)) : Prop :=
  OrbitProfileProductFull p.multiplicity criticalActionSubgroup H

section Flatten

variable (p : CriticalProfile) {ι : Type} (F : ι → Factor) (m : ι → ℕ)

abbrev FlatProduct := CriticalOriginal p × ((o : Σ i, Fin (m i)) → (F o.1).Carrier)

/-- Only curry/uncurry changes; all original occurrence labels survive. -/
def flatten : BinaryCarrierCriticalOccurrence.OriginalProduct p F m ≃* FlatProduct p F m :=
  (MulEquiv.refl (CriticalOriginal p)).prodCongr (curryOccurrences F m).symm

def decodeFlat (H : Subgroup (FlatProduct p F m)) :
    Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct p F m) :=
  H.comap (flatten p F m).toMonoidHom

theorem flatten_map_fst
    (H : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct p F m)) :
    (H.map (flatten p F m).toMonoidHom).map (MonoidHom.fst _ _) =
      H.map (MonoidHom.fst _ _) := by
  rw [Subgroup.map_map]
  rfl

theorem coordinateFull_flatten_iff
    (H : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct p F m)) :
    CarrierEpimorphismPullback.CoordinateFull (H.map (flatten p F m).toMonoidHom) ↔
      OccurrenceFull F m (H.map (MonoidHom.snd _ _)) := by
  constructor
  · intro h i j u
    obtain ⟨x, hx⟩ := h ⟨i, j⟩ u
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp x.2
    refine ⟨⟨z.2, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩⟩, ?_⟩
    exact (congrArg (fun y : FlatProduct p F m => y.2 ⟨i, j⟩) hzx).trans hx
  · intro h ⟨i, j⟩ u
    obtain ⟨x, hx⟩ := h i j u
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp x.2
    refine ⟨⟨flatten p F m z, Subgroup.mem_map.mpr ⟨z, hz, rfl⟩⟩, ?_⟩
    exact (congrArg (fun y : OccurrenceProduct F m => y i j) hzx).trans hx

/-- The generic pullback's exterior predicate is precisely original
individual critical fullness, not fullness of their whole product. -/
def originalFamilyEquivFlat
    (P : Subgroup (BinaryCarrierCriticalOccurrence.OriginalProduct p F m) → Prop) :
    BinaryCarrierCriticalOccurrence.OriginalFamily p F m P ≃
      CarrierEpimorphismPullback.OriginalFamily (criticalFull p)
        (fun H : Subgroup (FlatProduct p F m) => P (decodeFlat p F m H)) where
  toFun H := ⟨H.1.map (flatten p F m).toMonoidHom,
    (coordinateFull_flatten_iff p F m H.1).mpr H.2.1.2, by
      change criticalFull p ((H.1.map (flatten p F m).toMonoidHom).map _)
      rw [flatten_map_fst]
      exact H.2.1.1, by
      change P ((H.1.map (flatten p F m).toMonoidHom).comap
        (flatten p F m).toMonoidHom)
      rw [Subgroup.comap_map_eq_self_of_injective (flatten p F m).injective]
      exact H.2.2⟩
  invFun H := ⟨decodeFlat p F m H.1, ⟨by
      have hmap : (decodeFlat p F m H.1).map (flatten p F m).toMonoidHom = H.1 :=
        Subgroup.map_comap_eq_self_of_surjective (flatten p F m).surjective H.1
      have he := flatten_map_fst p F m (decodeFlat p F m H.1)
      rw [hmap] at he
      change criticalFull p ((decodeFlat p F m H.1).map _)
      rw [← he]
      exact H.2.2.1, by
      apply (coordinateFull_flatten_iff p F m _).mp
      rw [show (decodeFlat p F m H.1).map (flatten p F m).toMonoidHom = H.1 from
        Subgroup.map_comap_eq_self_of_surjective (flatten p F m).surjective H.1]
      exact H.2.1⟩, H.2.2.2⟩
  left_inv H := Subtype.ext
    (Subgroup.comap_map_eq_self_of_injective (flatten p F m).injective H.1)
  right_inv H := Subtype.ext
    (Subgroup.map_comap_eq_self_of_surjective (flatten p F m).surjective H.1)

end Flatten

section Mixed

variable {ι : Type} [Fintype ι] (Ω : ι → Type)
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)]
    (U : ∀ i, Subgroup (Equiv.Perm (Ω i)))
    (F : ι → Factor) (β : ∀ i, (F i).Carrier →* U i)
    (hβ : ∀ i, Function.Surjective (β i))

def targetBinary (i : ι) : IsPGroup 2 (U i) :=
  (F i).binary.of_surjective (β i) (hβ i)

def targetFactor (i : ι) : Factor :=
  BinaryCarrierMixedProfile.localFactor Ω U (targetBinary Ω U F β hβ) i

variable (p : CriticalProfile) (m : ι → ℕ)

def flatOriginalPredicate
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints Ω p m)) → Prop)
    (H : Subgroup (FlatProduct p (targetFactor Ω U F β hβ) m)) : Prop :=
  P (BinaryCarrierMixedProfile.decodeSplit Ω U (targetBinary Ω U F β hβ) p m
    (decodeFlat p (targetFactor Ω U F β hβ) m H))

def modelEquivFlat
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints Ω p m)) → Prop) :
    BinaryCarrierMixedProfile.ModelFamily Ω U p m P ≃
      CarrierEpimorphismPullback.OriginalFamily (criticalFull p)
        (flatOriginalPredicate Ω U F β hβ p m P) :=
  (BinaryCarrierMixedProfile.modelEquivSplit Ω U (targetBinary Ω U F β hβ) p m P).trans
    (originalFamilyEquivFlat p (targetFactor Ω U F β hβ) m
      (fun H => P (BinaryCarrierMixedProfile.decodeSplit Ω U
        (targetBinary Ω U F β hβ) p m H)))

abbrev MasterCoverFamily
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints Ω p m)) → Prop) :=
  CarrierEpimorphismPullback.CoverFamily (fun o : Σ i, Fin (m i) => β o.1)
    (criticalFull p) (flatOriginalPredicate Ω U F β hβ p m P)

/-- Original survival remains a predicate of the reconstructed subgroup in
this exact pullback family. Repeated occurrences are separate coordinates. -/
def modelEmbeddingCover
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints Ω p m)) → Prop) :
    BinaryCarrierMixedProfile.ModelFamily Ω U p m P ↪
      MasterCoverFamily Ω U F β hβ p m P :=
  (modelEquivFlat Ω U F β hβ p m P).toEmbedding.trans
    (CarrierEpimorphismPullback.familyEmbedding (fun o : Σ i, Fin (m i) => β o.1)
      (fun o => hβ o.1) (criticalFull p) (flatOriginalPredicate Ω U F β hβ p m P))

theorem modelEmbeddingCover_reconstruct
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints Ω p m)) → Prop)
    (K : BinaryCarrierMixedProfile.ModelFamily Ω U p m P) :
    (modelEmbeddingCover Ω U F β hβ p m P K).1.map
        (CarrierEpimorphismPullback.productMap (fun o : Σ i, Fin (m i) => β o.1)) =
      (modelEquivFlat Ω U F β hβ p m P K).1 :=
  CarrierEpimorphismPullback.familyEmbedding_reconstruct
    (fun o : Σ i, Fin (m i) => β o.1) (fun o => hβ o.1) (criticalFull p)
    (flatOriginalPredicate Ω U F β hβ p m P) (modelEquivFlat Ω U F β hβ p m P K)

/-- Forget only the extra decoded survival restriction when applying the
universal source-word count. All original critical and carrier fullness stays. -/
private def forgetCover
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints Ω p m)) → Prop) :
    MasterCoverFamily Ω U F β hβ p m P ↪
      CarrierEpimorphismPullback.OriginalFamily (criticalFull p)
        (fun _ : Subgroup (FlatProduct p F m) => True) where
  toFun H := ⟨H.1, H.2.1, H.2.2.1, True.intro⟩
  inj' := by
    intro H K h
    apply Subtype.ext
    exact congrArg
      (fun J : CarrierEpimorphismPullback.OriginalFamily (criticalFull p)
        (fun _ : Subgroup (FlatProduct p F m) => True) => J.1) h

def modelEmbeddingSourceFull
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints Ω p m)) → Prop) :
    BinaryCarrierMixedProfile.ModelFamily Ω U p m P ↪
      BinaryCarrierCriticalOccurrence.OriginalFamily p F m (fun _ => True) :=
  ((modelEmbeddingCover Ω U F β hβ p m P).trans
    (forgetCover Ω U F β hβ p m P)).trans
      (originalFamilyEquivFlat p F m (fun _ => True)).symm.toEmbedding

variable {L : ℕ} (occurrences : Fin L ≃ (Σ i, Fin (m i)))

include β hβ in
/-- Only the actual source master word needs the order/history certificate.
The original target model and its arbitrary predicate remain on the left. -/
theorem modelFamily_card_le_reserve (b : ℕ)
    (hb : OrderBound (occurrenceWord F m occurrences) b)
    (T : ℝ) (cert : CertifiedHistoryRows (occurrenceWord F m occurrences) T)
    (P : Subgroup (Equiv.Perm (BinaryCarrierMixedProfile.ModelPoints Ω p m)) → Prop) :
    (Nat.card (BinaryCarrierMixedProfile.ModelFamily Ω U p m P) : ℝ) ≤
      terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p) b L T := by
  have hmodel : Nat.card (BinaryCarrierMixedProfile.ModelFamily Ω U p m P) ≤
      Nat.card (BinaryCarrierCriticalOccurrence.OriginalFamily p F m (fun _ => True)) :=
    Nat.card_le_card_of_injective (modelEmbeddingSourceFull Ω U F β hβ p m P)
      (modelEmbeddingSourceFull Ω U F β hβ p m P).injective
  have hmodelReal : (Nat.card (BinaryCarrierMixedProfile.ModelFamily Ω U p m P) : ℝ) ≤
      (Nat.card (BinaryCarrierCriticalOccurrence.OriginalFamily p F m (fun _ => True)) : ℝ) := by
    exact_mod_cast hmodel
  apply hmodelReal.trans
  rw [BinaryCarrierCriticalOccurrence.originalFamily_card p F m occurrences (fun _ => True)]
  simpa only [occurrenceWord_length] using
    terminal_product_subgroups_le_reserve_of_orderBound p.abelianRank
      (criticalProfileNonabelianChoice p) (occurrenceWord F m occurrences) b hb T cert
      (BinaryCarrierCriticalOccurrence.terminalPredicate p F m occurrences (fun _ => True))

include β hβ in
/-- The original target normalizers and multiplicity factorials are used
unchanged. No normalizer of a source master occurs in this denominator. -/
theorem full_profile_card_le_reserve (b : ℕ)
    (hb : OrderBound (occurrenceWord F m occurrences) b)
    (T : ℝ) (cert : CertifiedHistoryRows (occurrenceWord F m occurrences) T)
    {X : Type*} (labels : BinaryCarrierMixedProfile.ModelPoints Ω p m ≃ X) :
    (Nat.card (FullOrbitProfileOn (BinaryCarrierMixedProfile.points Ω)
      (BinaryCarrierMixedProfile.multiplicity p m) (BinaryCarrierMixedProfile.action Ω U) X) : ℝ) ≤
      ((BinaryCarrierMixedProfile.physicalDegree Ω p m).factorial : ℝ) *
        terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p) b L T /
          BinaryCarrierMixedProfile.originalDenominator Ω U p m := by
  rw [← Nat.card_congr (assembledFullOrbitProfileEquiv
    (X := X) (m := BinaryCarrierMixedProfile.multiplicity p m)
    (BinaryCarrierMixedProfile.action Ω U))]
  have hmodel :
      (Nat.card {K // OrbitProfileFull (m := BinaryCarrierMixedProfile.multiplicity p m)
        (BinaryCarrierMixedProfile.action Ω U) 1 K} : ℝ) ≤
      terminalProductReserve p.abelianRank (criticalProfileNonabelianChoice p) b L T := by
    simpa only [BinaryCarrierMixedProfile.ModelFamily, and_true] using
      modelFamily_card_le_reserve Ω U F β hβ p m occurrences b hb T cert (fun _ => True)
  simpa only [BinaryCarrierMixedProfile.physicalDegree,
    BinaryCarrierMixedProfile.originalDenominator] using
    assembledOrbitProfileOn_card_le_real_of_model_bound
      (orbitProfileFull_family_natural (BinaryCarrierMixedProfile.multiplicity p m)
        (BinaryCarrierMixedProfile.action Ω U)) labels hmodel

end Mixed
end SymmetricSubgroupAsymptotics.BinaryCarrierMixedProfileEpimorphism
