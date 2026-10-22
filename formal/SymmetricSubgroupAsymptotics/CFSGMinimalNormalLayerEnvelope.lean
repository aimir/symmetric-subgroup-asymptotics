import SymmetricSubgroupAsymptotics.CFSGIrreducibleElementaryLayerEnvelope

/-! One Schur slope pays a complete elementary minimal normal layer, for
every original normal axis at once. Finite coordinates and irreducibility
are constructed from the actual minimal normal subgroup. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable {G : Type} [Group G] [Finite G]

theorem minimalNormalElementary_completeQuotientWeight
    (E : Subgroup G) [E.Normal] (C : ElementaryMinimalNormalChart E)
    (hne : E ≠ ⊥)
    (hmin : ∀ K : Subgroup G, K.Normal → K ≤ E → K = ⊥ ∨ K = E)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := G) J ≤
      elementaryLayerEnvelopeConstant C.p (QuotientGroup.mk' E)
        C.quotientRepresentation C.originalKernelChart *
      (C.p : ℝ) ^ ((b : ℝ) / C.p) *
      completeQuotientWeight (R := G ⧸ E) J := by
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    (fun _ _ h => Multiplicative.ofAdd.injective (C.equiv.symm.injective h))
  letI : Finite C.quotientRepresentation := inferInstanceAs (Finite C.V)
  simpa only [one_mul] using
    completeQuotientWeight_le_irreducibleLayer C.p (QuotientGroup.mk' E)
      (QuotientGroup.mk'_surjective E) C.quotientRepresentation C.originalKernelChart
      (C.quotientRepresentation_irreducible hne hmin) J

end SymmetricSubgroupAsymptotics
