import SymmetricSubgroupAsymptotics.Non2SectionCapacity
import SymmetricSubgroupAsymptotics.OriginalCentralCutFusion

/-!
# Counting-ready original-weight nonbinary fusion

The complete nonbinary section-capacity theorem chooses one retained central
cut.  This file packages that cut with the exact shifted degree, the positive
fusion gap, the common-source moment, and the unchanged original extension
envelope.  It is the reusable boundary for physical O03/O02 and c=1 owner
applications.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics

variable {B : Type} [Group B]

/-- One cut selected by complete nonbinary section capacity, retaining both
its module-theoretic properties and the numerical original-weight reserve. -/
structure Non2OriginalFusionCertificate
    (M : Rep (ZMod 2) B) (s : ℕ) where
  fixed_budget :
    16 * Module.finrank (ZMod 2) M.ρ.invariants ≤ 5 * s
  cut : {C : Submodule (ZMod 2) M // C ≤ M.ρ.invariants}
  cut_finrank : Module.finrank (ZMod 2) cut.1 =
    non2CentralCutDimension
      (Module.finrank (ZMod 2) M.ρ.invariants)
      (Module.finrank (ZMod 2)
        (displacementSlice M.ρ M.ρ.invariants))
  displacement_zero : displacementSlice M.ρ cut.1 = ⊥
  quotient_invariants :
    Module.finrank (ZMod 2)
        (OriginalCentralCutExtension.quotientModule M cut).ρ.invariants =
      Module.finrank (ZMod 2) M.ρ.invariants -
        non2CentralCutDimension
          (Module.finrank (ZMod 2) M.ρ.invariants)
          (Module.finrank (ZMod 2)
            (displacementSlice M.ρ M.ρ.invariants))
  cost_le :
    2 * (Module.finrank (ZMod 2) cut.1 : ℝ) +
        4 * OriginalCentralCutFusion.capacity M cut ≤
      47 * (s : ℝ) / 48
  gap_ge :
    (s : ℝ) / 768 ≤
      OriginalCentralCutFusion.gapParameter M cut (2 * s) s

namespace Non2OriginalFusionCertificate

variable {M : Rep (ZMod 2) B} {s : ℕ}

def prefixDegree (C : Non2OriginalFusionCertificate M s) : ℕ :=
  OriginalCentralCutFusion.prefixDegree M C.cut s

def markerHalf (C : Non2OriginalFusionCertificate M s) : ℕ :=
  s / 2 + Module.finrank (ZMod 2) C.cut.1

def liftConstant (C : Non2OriginalFusionCertificate M s) : ℝ :=
  OriginalCentralCutFusion.liftConstant M C.cut

def gapParameter (C : Non2OriginalFusionCertificate M s) : ℝ :=
  OriginalCentralCutFusion.gapParameter M C.cut (2 * s) s

def momentWeight (C : Non2OriginalFusionCertificate M s)
    (J : Type*) [Group J] : ℝ :=
  OriginalCentralCutFusion.momentWeight M C.cut J

theorem prefixDegree_eq_two_mul_markerHalf
    (C : Non2OriginalFusionCertificate M s) (heven : Even s) :
    C.prefixDegree = 2 * C.markerHalf := by
  obtain ⟨k, hk⟩ := heven
  unfold prefixDegree markerHalf OriginalCentralCutFusion.prefixDegree
  omega

/-- The retained cut is at most half the fixed space.  Together with the
`5/16` permutation-section bound, this puts the shifted half-width below
`21/32` of the original half-width.  This is the quantitative prefix bound
used by the varying-width direct aggregate. -/
theorem markerHalf_strong
    (C : Non2OriginalFusionCertificate M s) :
    32 * C.markerHalf ≤ 21 * s := by
  let t := Module.finrank (ZMod 2) M.ρ.invariants
  let ell := Module.finrank (ZMod 2)
    (displacementSlice M.ρ M.ρ.invariants)
  have hcut : 2 * Module.finrank (ZMod 2) C.cut.1 ≤ t := by
    rw [C.cut_finrank]
    exact non2CentralCutDimension_le_half t ell
  have hfixed := C.fixed_budget
  unfold markerHalf
  dsimp only [t] at hcut hfixed
  omega

theorem prefixDegree_lt [Finite M]
    (C : Non2OriginalFusionCertificate M s) (hs : 24 ≤ s) :
    C.prefixDegree < 2 * s := by
  apply OriginalCentralCutFusion.prefixDegree_lt_of_cost M C.cut s
  have hspos : 0 < (s : ℝ) := by
    exact_mod_cast (show 0 < s by omega)
  linarith [C.cost_le]

theorem liftConstant_nonneg
    (C : Non2OriginalFusionCertificate M s) :
    0 ≤ C.liftConstant :=
  OriginalCentralCutFusion.liftConstant_nonneg M C.cut

theorem gapParameter_pos
    (C : Non2OriginalFusionCertificate M s) (hs : 24 ≤ s) :
    0 < C.gapParameter := by
  have hspos : 0 < (s : ℝ) := by
    exact_mod_cast (show 0 < s by omega)
  exact lt_of_lt_of_le (by positivity : 0 < (s : ℝ) / 768) C.gap_ge

/-- The retained marker and every repeated base map remain in one complete
source.  No independent-orbit or product-image hypothesis is introduced. -/
theorem momentWeight_moment_le
    (C : Non2OriginalFusionCertificate M s)
    {T : Type} [Group T]
    (ρ : T →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (σ : T →* B) (hσ : Function.Surjective σ)
    (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), C.momentWeight J ^ q) ≤
      (subgroupCount (b + q * C.prefixDegree) : ℝ) := by
  exact OriginalCentralCutFusion.momentWeight_moment_le M C.cut
    ρ hρ σ hσ b q

/-- The complete actual surviving family keeps the original nonsplit
extension and arbitrary original survival predicate. -/
theorem original_survival_localFactor_le [Finite B] [Finite M]
    (C : Non2OriginalFusionCertificate M s)
    {Q : Type} [Group Q] [Finite Q]
    (π : Q →* B) (hπ : Function.Surjective π)
    (E : OriginalKernelModuleChart π M)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b)))
    (S : GroupEpimorphism J Q → Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f} : ℝ) ≤
      fusionLocalFactor b s C.prefixDegree C.liftConstant C.gapParameter *
        C.momentWeight J := by
  exact OriginalCentralCutFusion.original_survival_localFactor_le
    M C.cut π hπ E s s J S

/-- Physical form of the envelope for one literal original normal axis.
The predicate is evaluated on the same Goursat reconstruction used by the
original-weight family count. -/
theorem fusionSurvivingEpiCount_le [Finite B] [Finite M]
    (C : Non2OriginalFusionCertificate M s)
    (U : Subgroup (Equiv.Perm (Fin (2 * s))))
    (N : {N : Subgroup U // N.Normal})
    (π : (U ⧸ N.1) →* B) (hπ : Function.Surjective π)
    (E : OriginalKernelModuleChart π M)
    {b : ℕ} (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤
      fusionLocalFactor b s C.prefixDegree C.liftConstant C.gapParameter *
        C.momentWeight J := by
  exact C.original_survival_localFactor_le π hπ E J
    (fun f => P (fusionFullGoursatEncode N J f).1)

/-- Direct first-moment physical fusion for a complete family of literal
normal axes.  Each axis may have its own nonbinary quotient, section, cut,
faithful top cover and nonsplit extension chart; the original action
normalizer is charged only by the physical counting theorem. -/
theorem physical_direct_bound
    (U : Subgroup (Equiv.Perm (Fin (2 * s)))) (b : ℕ)
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (hP : FusionOrbitNatural U P)
    (B₀ : {N : Subgroup U // N.Normal} → Type)
    [∀ N, Group (B₀ N)] [∀ N, Finite (B₀ N)]
    (M₀ : ∀ N, Rep (ZMod 2) (B₀ N))
    [∀ N, Finite (M₀ N)]
    (C₀ : ∀ N, Non2OriginalFusionCertificate (M₀ N) s)
    (π : ∀ N, (U ⧸ N.1) →* B₀ N)
    (hπ : ∀ N, Function.Surjective (π N))
    (E : ∀ N, OriginalKernelModuleChart (π N) (M₀ N))
    (T : {N : Subgroup U // N.Normal} → Type)
    [∀ N, Group (T N)]
    (ρ : ∀ N, T N →* Equiv.Perm (Fin s))
    (hρ : ∀ N, Function.Injective (ρ N))
    (σ : ∀ N, T N →* B₀ N)
    (hσ : ∀ N, Function.Surjective (σ N)) :
    (Nat.card (FusionOrbitFamily U (FusionAcceptedOrbitPredicate U P)) : ℝ) /
        exactBenchmark (b + 2 * s) ≤
      ∑ N : {N : Subgroup U // N.Normal},
        fusionDirectKernel b s (C₀ N).prefixDegree (C₀ N).liftConstant
          (Nat.card (Subgroup.normalizer
            (U : Set (Equiv.Perm (Fin (2 * s))))) : ℝ)
          (C₀ N).gapParameter *
            ((subgroupCount (b + (C₀ N).prefixDegree) : ℝ) /
              exactBenchmark (b + (C₀ N).prefixDegree)) := by
  apply SymmetricSubgroupAsymptotics.fusionPhysical_direct_bound
    U b P hP
      (fun N => (C₀ N).prefixDegree)
      (fun N => (C₀ N).liftConstant)
      (fun N => (C₀ N).gapParameter)
      (fun N J => (C₀ N).momentWeight J)
  · intro N
    exact (C₀ N).liftConstant_nonneg
  · intro N J
    exact (C₀ N).fusionSurvivingEpiCount_le
      U N (π N) (hπ N) (E N) P J
  · intro N
    simpa only [pow_one, one_mul] using
      (C₀ N).momentWeight_moment_le
        (ρ N) (hρ N) (σ N) (hσ N) b 1

end Non2OriginalFusionCertificate

variable {X : Type} [Finite B] [Finite X] [MulAction B X] [FaithfulSMul B X]
    [MulAction.IsPretransitive B X]

/-- Complete construction of the reusable counting-ready certificate from
the two named Tracey inputs and the original permutation quotient. -/
theorem exists_non2OriginalFusionCertificate
    (hTracey : TraceyBinaryFormulaInput)
    (hExceptional : TraceyBinaryExceptionalThreeInput)
    (hB : ¬IsPGroup 2 B) (x : X)
    (M : Rep (ZMod 2) B) [FiniteDimensional (ZMod 2) M]
    (P : Subrepresentation
      (permutationFunctionRepresentation (ZMod 2) B X))
    (qmap : P.toRepresentation.IntertwiningMap M.ρ)
    (hqmap : Function.Surjective qmap)
    (hs : 24 ≤ Nat.card X) (heven : Even (Nat.card X)) :
    Nonempty (Non2OriginalFusionCertificate M (Nat.card X)) := by
  have hfixed :
      16 * Module.finrank (ZMod 2) M.ρ.invariants ≤ 5 * Nat.card X :=
    binary_permutationSection_invariants_five_sixteenths
      hTracey hExceptional M.ρ P qmap hqmap hs
  obtain ⟨C, hCdim, hzero, hQfixed, hcost, hgap⟩ :=
    exists_non2SectionCapacity_cut_of_Tracey_inputs_full
      hTracey hExceptional hB x M P qmap hqmap hs heven
  exact ⟨{
    fixed_budget := hfixed
    cut := C
    cut_finrank := hCdim
    displacement_zero := hzero
    quotient_invariants := hQfixed
    cost_le := hcost
    gap_ge := hgap }⟩

end SymmetricSubgroupAsymptotics

end
