import SymmetricSubgroupAsymptotics.BinaryPhysicalPairMoments
import SymmetricSubgroupAsymptotics.BinaryPairPrefixChart
import SymmetricSubgroupAsymptotics.PermutationTwoGroupRank
import SymmetricSubgroupAsymptotics.FusionFiniteMenu

/-! The physical pair envelope on each complete original exterior subgroup.
The permutation two-group rank theorem supplies the actual Sylow-kernel
rank bound. The translation and H1 factors, original normal quotient and
all survival predicates are retained. The canonical weight is the same
weight whose shared-source moments are proved in BinaryPhysicalPairMoments.
-/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {N : Subgroup U} [N.Normal]
    (C : BinaryPhysicalPairCertificate U N)

/-- The actual post-cut module in the original nonsplit extension tower. -/
abbrev liftModule := C.localCertificate.prefixModule
  (F := C.frame) (N := N) (generators := C.generators) (hgen := C.generators_full)

/-- Both the translation and first-cohomology factors are kept explicitly. -/
def liftConstant : ℝ :=
  (Nat.card C.liftModule : ℝ) * Nat.card (groupCohomology.H1 C.liftModule)

theorem liftConstant_nonneg : 0 ≤ C.liftConstant := by
  unfold liftConstant
  positivity

/-- An arbitrary surviving original epimorphism has the certified pair
bound, without an assumed permutation rank or local counting envelope. -/
theorem original_survival_card_le {b : ℕ} (hU : IsPGroup 2 U)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (S : GroupEpimorphism J (U ⧸ N) → Prop) :
    (Nat.card {f : GroupEpimorphism J (U ⧸ N) // S f} : ℝ) ≤
      C.liftConstant * (2 : ℝ)^((C.localCertificate.fixedDimension : ℝ)/2*(b : ℝ)) *
        C.momentWeight J := by
  classical
  let P : ∀ β : GroupEpimorphism J C.momentQuotient, Sylow 2 β.1.ker :=
    fun _ => Classical.arbitrary _
  have hrank : ∀ β : GroupEpimorphism J C.momentQuotient,
      (Module.finrank (ZMod 2) (PrimeAbelianization 2 (P β : Subgroup β.1.ker)) : ℝ) ≤
        (b : ℝ)/2 := fun β =>
    permutationTwoGroup_sylowKernel_primeAbelianizationRank_le J β.1 (P β)
  have h := C.localCertificate.prefix_survival_card_le C.frame N C.generators
    C.generators_full hU P S (b : ℝ) hrank
  simpa only [liftConstant, liftModule, momentWeight, momentQuotient,
    fusionCentralPrefixWeight] using h

/-- The same estimate on the exact surviving count used by physical fusion.
The full original graph determines survival; its exterior source stays J. -/
theorem original_survivingEpiCount_le {b : ℕ} (hU : IsPGroup 2 U)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P ⟨N, inferInstance⟩ J ≤
      C.liftConstant * (2 : ℝ)^((C.localCertificate.fixedDimension : ℝ)/2*(b : ℝ)) *
        C.momentWeight J :=
  C.original_survival_card_le hU J
    (fun f => P (fusionFullGoursatEncode ⟨N, inferInstance⟩ J f).1)

end SymmetricSubgroupAsymptotics.BinaryPhysicalPairCertificate
