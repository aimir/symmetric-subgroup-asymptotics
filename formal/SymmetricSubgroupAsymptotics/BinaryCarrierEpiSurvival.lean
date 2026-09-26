import SymmetricSubgroupAsymptotics.BinaryCarrierSurvival
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport
import SymmetricSubgroupAsymptotics.FusionFiniteMenu

/-! Fixed-complete-source carrier transport for the original surviving
epimorphism count. The literal exterior subgroup J is unchanged, and the
target is identified through the checked original quotient map. Survival
is tested on the inverse reconstructed original subgroup. An intrinsic
carrier predicate can bound that count only after its acceptance implication
and its own envelope have been supplied; no physical owner is inferred. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics.CheckedPermutationCarrier

variable {w q : ℕ} (C : CheckedPermutationCarrier w q)
    {U : Subgroup (Equiv.Perm (Fin w))} (hsource : C.source = U)
    {E : Type*} [Group E]

/-- The same literal complete exterior source, with only the actual
original quotient changed by its checked equivalence. -/
def originalEpiEquiv (N : Subgroup U) [N.Normal]
    (haxis : C.axis = N.map U.subtype) (J : Subgroup E) :
    GroupEpimorphism J (U ⧸ N) ≃ GroupEpimorphism J C.quotient :=
  fusionGroupEpimorphismCongr (MulEquiv.refl J)
    (C.originalQuotientEquiv hsource N haxis)

@[simp] theorem originalEpiEquiv_apply (N : Subgroup U) [N.Normal]
    (haxis : C.axis = N.map U.subtype) (J : Subgroup E)
    (γ : GroupEpimorphism J (U ⧸ N)) (j : J) :
    (C.originalEpiEquiv hsource N haxis J γ).1 j =
      C.originalQuotientEquiv hsource N haxis (γ.1 j) := rfl

/-- The quotient change retains the exact graph inside the original
product, rather than just an abstract isomorphism type. -/
theorem originalEpiGraph_eq (N : Subgroup U) [N.Normal]
    (haxis : C.axis = N.map U.subtype) (J : Subgroup E)
    (γ : GroupEpimorphism J (U ⧸ N)) :
    fusionQuotientGraph (QuotientGroup.mk' N) J γ.1 =
      fusionQuotientGraph (C.originalAlpha hsource) J
        (C.originalEpiEquiv hsource N haxis J γ).1 := by
  ext x
  constructor
  · rintro ⟨j, hj, hγ⟩
    refine ⟨j, hj, ?_⟩
    change C.originalQuotientEquiv hsource N haxis (QuotientGroup.mk x.1) =
      C.originalQuotientEquiv hsource N haxis (γ.1 j)
    exact congrArg (C.originalQuotientEquiv hsource N haxis) hγ
  · rintro ⟨j, hj, hγ⟩
    refine ⟨j, hj, ?_⟩
    apply (C.originalQuotientEquiv hsource N haxis).injective
    exact hγ

/-- The epi equivalence agrees with the literal checked carrier transport. -/
theorem originalEpiGraph_transport (N : Subgroup U) [N.Normal]
    (haxis : C.axis = N.map U.subtype) (J : Subgroup E)
    (γ : GroupEpimorphism J (U ⧸ N)) :
    C.transportOriginal hsource
      (fusionQuotientGraph (QuotientGroup.mk' N) J γ.1) =
      fusionQuotientGraph C.beta J (C.originalEpiEquiv hsource N haxis J γ).1 := by
  rw [C.originalEpiGraph_eq hsource N haxis J γ]
  exact C.transportOriginal_quotientGraph hsource J _

/-- Every exterior correlation is recovered with the original maps. -/
theorem originalEpiGraph_reconstruct (N : Subgroup U) [N.Normal]
    (haxis : C.axis = N.map U.subtype) (J : Subgroup E)
    (γ : GroupEpimorphism J (U ⧸ N)) :
    ((fusionQuotientGraph C.beta J
      (C.originalEpiEquiv hsource N haxis J γ).1).map C.carrierMap).comap
        (C.originalSourceMap hsource) =
      fusionQuotientGraph (QuotientGroup.mk' N) J γ.1 := by
  rw [← C.originalEpiGraph_transport hsource N haxis J γ]
  apply C.transportOriginal_reconstruct hsource N haxis
  intro u hu
  apply Subgroup.mem_goursatFst.mp
  rw [fusionQuotientGraph_axis, QuotientGroup.ker_mk']
  exact hu

/-- This carrier predicate retains all survival conditions on the inverse
original subgroup. It does not assert acceptance by an intrinsic owner. -/
def carrierInverseSurvival (P : Subgroup (U × E) → Prop)
    (L : Subgroup (C.carrier × E)) : Prop :=
  P ((L.map C.carrierMap).comap (C.originalSourceMap hsource))

/-- Agreement with the full pointed-family survival equivalence. -/
theorem carrierInverseSurvival_pointed (P : Subgroup (U × E) → Prop)
    (L : FusionPointedSubgroups C.beta E) :
    C.carrierInverseSurvival hsource P L.1 ↔
      P (((C.originalPointedEquiv hsource).symm L).1) := by
  rw [C.originalPointedEquiv_symm_val hsource L]
  rfl

/-- Exact surviving-epi bijection for each fixed literal J. No automorphism
factor is divided out, and no summation changes the complete source. -/
def originalSurvivingEpiEquiv (N : Subgroup U) [N.Normal]
    (haxis : C.axis = N.map U.subtype) (J : Subgroup E)
    (P : Subgroup (U × E) → Prop) :
    {γ : GroupEpimorphism J (U ⧸ N) //
      P (fusionQuotientGraph (QuotientGroup.mk' N) J γ.1)} ≃
    {δ : GroupEpimorphism J C.quotient //
      C.carrierInverseSurvival hsource P (fusionQuotientGraph C.beta J δ.1)} :=
  (C.originalEpiEquiv hsource N haxis J).subtypeEquiv (fun γ => by
    change P (fusionQuotientGraph (QuotientGroup.mk' N) J γ.1) ↔
      P (((fusionQuotientGraph C.beta J
        (C.originalEpiEquiv hsource N haxis J γ).1).map C.carrierMap).comap
          (C.originalSourceMap hsource))
    rw [C.originalEpiGraph_reconstruct hsource N haxis J γ])

theorem originalSurvivingEpi_card (N : Subgroup U) [N.Normal]
    (haxis : C.axis = N.map U.subtype) (J : Subgroup E)
    (P : Subgroup (U × E) → Prop) :
    Nat.card {γ : GroupEpimorphism J (U ⧸ N) //
      P (fusionQuotientGraph (QuotientGroup.mk' N) J γ.1)} =
    Nat.card {δ : GroupEpimorphism J C.quotient //
      C.carrierInverseSurvival hsource P (fusionQuotientGraph C.beta J δ.1)} :=
  Nat.card_congr (C.originalSurvivingEpiEquiv hsource N haxis J P)

section Weighted

local instance [Finite E] {T : Type*} [Group T] [Finite T]
    (J : Subgroup E) : Fintype (GroupEpimorphism J T) := Fintype.ofFinite _

/-- Arbitrary original weights are preserved within the same J fiber. -/
theorem originalSurvivingEpi_weighted_sum [Fintype E]
    {M : Type*} [AddCommMonoid M] (N : Subgroup U) [N.Normal]
    (haxis : C.axis = N.map U.subtype) (J : Subgroup E)
    (P : Subgroup (U × E) → Prop) (W : Subgroup (U × E) → M) :
    (∑ γ : {γ : GroupEpimorphism J (U ⧸ N) //
      P (fusionQuotientGraph (QuotientGroup.mk' N) J γ.1)},
      W (fusionQuotientGraph (QuotientGroup.mk' N) J γ.1.1)) =
    ∑ δ : {δ : GroupEpimorphism J C.quotient //
      C.carrierInverseSurvival hsource P (fusionQuotientGraph C.beta J δ.1)},
      W (((fusionQuotientGraph C.beta J δ.1.1).map C.carrierMap).comap
        (C.originalSourceMap hsource)) := by
  have h := (C.originalSurvivingEpiEquiv hsource N haxis J P).sum_comp
    (fun δ => W (((fusionQuotientGraph C.beta J δ.1.1).map C.carrierMap).comap
      (C.originalSourceMap hsource)))
  simpa only [originalSurvivingEpiEquiv, Equiv.subtypeEquiv_apply,
    C.originalEpiGraph_reconstruct hsource N haxis J] using h

end Weighted

/-- An intrinsic carrier family can be used only with an explicit
acceptance implication for these inverse-original survivors. -/
theorem originalSurvivingEpi_card_le_of_carrier [Finite E]
    (N : Subgroup U) [N.Normal] (haxis : C.axis = N.map U.subtype)
    (J : Subgroup E) (P : Subgroup (U × E) → Prop)
    (R : Subgroup (C.carrier × E) → Prop)
    (haccept : ∀ δ : GroupEpimorphism J C.quotient,
      C.carrierInverseSurvival hsource P (fusionQuotientGraph C.beta J δ.1) →
        R (fusionQuotientGraph C.beta J δ.1)) :
    Nat.card {γ : GroupEpimorphism J (U ⧸ N) //
      P (fusionQuotientGraph (QuotientGroup.mk' N) J γ.1)} ≤
    Nat.card {δ : GroupEpimorphism J C.quotient //
      R (fusionQuotientGraph C.beta J δ.1)} := by
  rw [C.originalSurvivingEpi_card hsource N haxis J P]
  let f : {δ : GroupEpimorphism J C.quotient //
      C.carrierInverseSurvival hsource P (fusionQuotientGraph C.beta J δ.1)} →
      {δ : GroupEpimorphism J C.quotient //
        R (fusionQuotientGraph C.beta J δ.1)} :=
    fun δ => ⟨δ.1, haccept δ.1 δ.2⟩
  apply Nat.card_le_card_of_injective f
  intro δ ε he
  apply Subtype.ext
  exact congrArg (fun z : {δ : GroupEpimorphism J C.quotient //
    R (fusionQuotientGraph C.beta J δ.1)} => z.1) he

section PhysicalExterior
variable {Z : Type*}

/-- The exact per-source count occurring in BinaryFiniteEntryFusion. -/
theorem originalSurvivingEpiCount_eq
    (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (N : {N : Subgroup U // N.Normal}) (haxis : C.axis = N.1.map U.subtype)
    (J : Subgroup (Equiv.Perm Z)) :
    fusionSurvivingEpiCount U P N J =
      (Nat.card {δ : GroupEpimorphism J C.quotient //
        C.carrierInverseSurvival hsource P (fusionQuotientGraph C.beta J δ.1)} : ℝ) := by
  exact congrArg (fun n : ℕ => (n : ℝ))
    (C.originalSurvivingEpi_card hsource N.1 haxis J P)

/-- An explicit intrinsic carrier envelope supplies the original hcarrier
bound, with its same complete source J and original survival retained. -/
theorem originalSurvivingEpiCount_le_of_carrier_envelope [Finite Z]
    (P : Subgroup (U × Equiv.Perm Z) → Prop)
    (N : {N : Subgroup U // N.Normal}) (haxis : C.axis = N.1.map U.subtype)
    (J : Subgroup (Equiv.Perm Z))
    (R : Subgroup (C.carrier × Equiv.Perm Z) → Prop)
    (haccept : ∀ δ : GroupEpimorphism J C.quotient,
      C.carrierInverseSurvival hsource P (fusionQuotientGraph C.beta J δ.1) →
        R (fusionQuotientGraph C.beta J δ.1))
    (B : ℝ) (henvelope :
      (Nat.card {δ : GroupEpimorphism J C.quotient //
        R (fusionQuotientGraph C.beta J δ.1)} : ℝ) ≤ B) :
    fusionSurvivingEpiCount U P N J ≤ B := by
  have h := C.originalSurvivingEpi_card_le_of_carrier hsource N.1 haxis J P R haccept
  have hR : (Nat.card {γ : GroupEpimorphism J (U ⧸ N.1) //
      P (fusionQuotientGraph (QuotientGroup.mk' N.1) J γ.1)} : ℝ) ≤
      (Nat.card {δ : GroupEpimorphism J C.quotient //
        R (fusionQuotientGraph C.beta J δ.1)} : ℝ) := by exact_mod_cast h
  exact hR.trans henvelope

end PhysicalExterior
end SymmetricSubgroupAsymptotics.CheckedPermutationCarrier
