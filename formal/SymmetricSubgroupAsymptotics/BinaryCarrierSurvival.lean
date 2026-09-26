import SymmetricSubgroupAsymptotics.BinaryCarrierOriginal
import SymmetricSubgroupAsymptotics.FusionGoursatCount

/-! A checked carrier gives an exact bijection of the full original
fixed-axis families. It agrees with literal map/comap transport and retains
arbitrary predicates and weights on the reconstructed original subgroup.
This does not assert that a carrier belongs to an earlier counting owner. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.CheckedPermutationCarrier

variable {w q : ℕ} (C : CheckedPermutationCarrier w q)
    {U : Subgroup (Equiv.Perm (Fin w))} (hsource : C.source = U)
    {E : Type*} [Group E]

/-- Literal transport preserves the complete complement and its actual
map to the common quotient, including when the carrier is subdirect. -/
theorem transportOriginal_quotientGraph (J : Subgroup E) (γ : J →* C.quotient) :
    C.transportOriginal hsource
      (fusionQuotientGraph (C.originalAlpha hsource) J γ) =
      fusionQuotientGraph C.beta J γ := by
  ext x
  constructor
  · rintro ⟨y, ⟨j, hj, hγ⟩, he⟩
    have hfirst : C.originalAlpha hsource y.1 = C.beta x.1 :=
      congrArg Prod.fst he
    have hsecond : y.2 = x.2 := congrArg Prod.snd he
    exact ⟨j, hj.trans hsecond, hfirst.symm.trans hγ⟩
  · rintro ⟨j, hj, hγ⟩
    obtain ⟨u, hu⟩ := C.originalAlpha_surjective hsource (C.beta x.1)
    exact ⟨(u, x.2), ⟨j, hj, hu.trans hγ⟩, Prod.ext hu rfl⟩

/-- Both sides use the same literal Goursat data. No quotient automorphism
factor or information about the exterior is discarded. -/
def originalPointedEquiv :
    FusionPointedSubgroups (C.originalAlpha hsource) E ≃
      FusionPointedSubgroups C.beta E :=
  (fusionGoursatEquiv (C.originalAlpha hsource)
    (C.originalAlpha_surjective hsource)).trans
      (fusionGoursatEquiv C.beta C.beta_surjective).symm

@[simp] theorem originalPointedEquiv_encode (d : FusionGoursatData E C.quotient) :
    C.originalPointedEquiv hsource
      (fusionGoursatEncode (C.originalAlpha hsource) d) =
      fusionGoursatEncode C.beta d := by
  change (fusionGoursatEquiv C.beta C.beta_surjective).symm
    ((fusionGoursatEquiv (C.originalAlpha hsource) (C.originalAlpha_surjective hsource))
      ((fusionGoursatEquiv (C.originalAlpha hsource)
        (C.originalAlpha_surjective hsource)).symm d)) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The abstract equivalence is precisely the checked physical transport. -/
theorem originalPointedEquiv_val
    (H : FusionPointedSubgroups (C.originalAlpha hsource) E) :
    (C.originalPointedEquiv hsource H).1 = C.transportOriginal hsource H.1 := by
  obtain ⟨d, rfl⟩ := fusionGoursatEncode_surjective (C.originalAlpha hsource)
    (C.originalAlpha_surjective hsource) H
  rw [C.originalPointedEquiv_encode hsource]
  exact (C.transportOriginal_quotientGraph hsource d.1 d.2.1).symm

/-- The inverse reconstructs the original subgroup through the same two
quotient maps. Its original axis is identified by `originalAlpha_kernel`. -/
theorem originalPointedEquiv_symm_val
    (L : FusionPointedSubgroups C.beta E) :
    ((C.originalPointedEquiv hsource).symm L).1 =
      (L.1.map C.carrierMap).comap (C.originalSourceMap hsource) := by
  let H := (C.originalPointedEquiv hsource).symm L
  have htransport : C.transportOriginal hsource H.1 = L.1 := by
    rw [← C.originalPointedEquiv_val hsource H]
    exact congrArg Subtype.val ((C.originalPointedEquiv hsource).apply_symm_apply L)
  have hker : (C.originalSourceMap (E := E) hsource).ker ≤ H.1 := by
    rintro ⟨u, e⟩ he
    have he1 : e = 1 := congrArg Prod.snd he
    have hu : C.originalAlpha hsource u = 1 := congrArg Prod.fst he
    have haxis : u ∈ H.1.goursatFst := by rw [H.2.2]; exact hu
    rw [he1]
    exact Subgroup.mem_goursatFst.mp haxis
  rw [← htransport, transportOriginal,
    Subgroup.map_comap_eq_self_of_surjective C.carrierMap_surjective,
    Subgroup.comap_map_eq_self hker]

/-- Every survival condition is pulled back to the exact original subgroup.
No closure of that condition under carrier replacement is assumed. -/
def originalSurvivalEquiv (P : Subgroup (U × E) → Prop) :
    {H : FusionPointedSubgroups (C.originalAlpha hsource) E // P H.1} ≃
      {L : FusionPointedSubgroups C.beta E //
        P (((C.originalPointedEquiv hsource).symm L).1)} :=
  (C.originalPointedEquiv hsource).subtypeEquiv (fun H => by
    rw [Equiv.symm_apply_apply])

theorem originalSurvival_card (P : Subgroup (U × E) → Prop) :
    Nat.card {H : FusionPointedSubgroups (C.originalAlpha hsource) E // P H.1} =
      Nat.card {L : FusionPointedSubgroups C.beta E //
        P (((C.originalPointedEquiv hsource).symm L).1)} :=
  Nat.card_congr (C.originalSurvivalEquiv hsource P)

/-- Arbitrary weights on the original subgroup are retained, so this can
be used before any original-normalizer factor or later moment is applied. -/
theorem originalSurvival_weighted_sum [Fintype E]
    (P : Subgroup (U × E) → Prop) (W : Subgroup (U × E) → ℝ) :
    (∑ H : {H : FusionPointedSubgroups (C.originalAlpha hsource) E // P H.1},
      W H.1.1) =
    ∑ L : {L : FusionPointedSubgroups C.beta E //
      P (((C.originalPointedEquiv hsource).symm L).1)},
      W (((C.originalPointedEquiv hsource).symm L.1).1) := by
  have h := (C.originalSurvivalEquiv hsource P).sum_comp
    (fun L => W (((C.originalPointedEquiv hsource).symm L.1).1))
  simpa only [originalSurvivalEquiv, Equiv.subtypeEquiv_apply,
    Equiv.symm_apply_apply] using h

end SymmetricSubgroupAsymptotics.CheckedPermutationCarrier
