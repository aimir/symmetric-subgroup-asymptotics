import SymmetricSubgroupAsymptotics.BinaryPairZeroCutExtension
import SymmetricSubgroupAsymptotics.BinaryPairSectionInvariantBound
import SymmetricSubgroupAsymptotics.BinaryPairSectionCocycleBound
import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport
import SymmetricSubgroupAsymptotics.BinaryZeroCutWideParameters
import SymmetricSubgroupAsymptotics.PermutationTwoGroupRank
import SymmetricSubgroupAsymptotics.FusionDirectKernelAssembly

/-! Actual zero-cut envelopes and shared-source moments for every original
normal axis of a pair frame. The faithful prefix is the actual top group
covering the quotient, not a claimed faithful quotient action. The actual
Schur capacity determines the gap and is bounded internally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I : Type} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U I) (N : Subgroup U) [N.Normal]

def zeroCutCapacity : ℝ := representationSchurCapacity (F.zeroCutModule N).ρ

def zeroCutLiftConstant : ℝ :=
  (Nat.card (F.zeroCutModule N) : ℝ) * Nat.card (groupCohomology.H1 (F.zeroCutModule N))

def zeroCutGapParameter : ℝ :=
  ((Nat.card X : ℝ)-(Nat.card I : ℝ)-4*F.zeroCutCapacity N)/16

def zeroCutMomentWeight (J : Type*) [Group J] : ℝ :=
  Nat.card (GroupEpimorphism J (U ⧸ (F.top.ker⊔N)))

theorem zeroCutLiftConstant_nonneg : 0≤F.zeroCutLiftConstant N := by
  unfold zeroCutLiftConstant
  positivity

/-- Quotienting by the actual zero cut does not create any new fixed
directions. The inverse zero-quotient chart is injective on invariants. -/
theorem zeroCut_invariants_finrank_le [Finite I] :
    Module.finrank (ZMod 2) (F.zeroCutModule N).ρ.invariants≤
      Module.finrank (ZMod 2) (F.sectionRepresentation N).invariants := by
  let A := F.kernelSpace ⧸ F.normalSpace N
  letI : Finite A :=
    Finite.of_surjective (F.normalSpace N).mkQ (F.normalSpace N).mkQ_surjective
  let e : F.zeroCutModule N ≃ₗ[ZMod 2] A :=
    (⊥ : Submodule (ZMod 2) A).quotEquivOfEqBot rfl
  have hequiv (g : U ⧸ (F.top.ker⊔N)) (v : F.zeroCutModule N) :
      e ((F.zeroCutModule N).ρ g v)=F.sectionRepresentation N g (e v) := by
    obtain ⟨a,rfl⟩ := (⊥ : Submodule (ZMod 2) A).mkQ_surjective v
    change e ((⊥ : Submodule (ZMod 2) A).mkQ (F.sectionRepresentation N g a))=
      F.sectionRepresentation N g (e ((⊥ : Submodule (ZMod 2) A).mkQ a))
    rfl
  let L : (F.zeroCutModule N).ρ.invariants →ₗ[ZMod 2]
      (F.sectionRepresentation N).invariants :=
    (e.toLinearMap.comp (F.zeroCutModule N).ρ.invariants.subtype).codRestrict
      (F.sectionRepresentation N).invariants (fun v g =>
        (hequiv g v).symm.trans (congrArg e (v.property g)))
  have hL : Function.Injective L := by
    intro v w hvw
    apply Subtype.ext
    exact e.injective (congrArg Subtype.val hvw)
  exact LinearMap.finrank_le_finrank_of_injective hL

/-- The capacity is that of the actual original acting quotient and
zero-cut module; its bound is derived, not supplied as an acceptance field. -/
theorem zeroCutCapacity_le [Finite X] [Finite I]
    [MulAction.IsPretransitive F.top.range I] (hU : IsPGroup 2 U)
    (k : ℕ) (hI : Nat.card I=2^k) :
    F.zeroCutCapacity N≤(k.choose (k/2) : ℝ) := by
  unfold zeroCutCapacity
  rw [pGroup_representationSchurCapacity (hU.to_quotient (F.top.ker⊔N))]
  exact_mod_cast (F.zeroCut_invariants_finrank_le N).trans
    (F.section_invariants_finrank_le_of_top N hU k hI)

/-- All sufficiently large physical pair widths have the proved direct
wide-row gap, for every original normal, using the literal zero cut. -/
theorem zeroCut_wide_parameters [Finite X] [Finite I]
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (k : ℕ) (hk : 11≤k) (hI : Nat.card I=2^k) :
    16*Nat.card I≤13*Nat.card X ∧ Nat.card I<Nat.card X ∧
      0<F.zeroCutGapParameter N ∧
      (Nat.card X : ℝ)/32≤16*F.zeroCutGapParameter N := by
  letI : MulAction.IsPretransitive F.top.range I := F.top_pretransitive
  have hr := F.zeroCutCapacity_le N hU k hI
  have hgap := binary_zeroCut_direct_gap k hk (F.zeroCutCapacity N) hr
  have hX := F.card_points
  have hp : 0<2^k := pow_pos (by decide) _
  refine ⟨by rw [hX,hI]; omega,by rw [hX,hI]; omega,?_⟩
  simpa only [zeroCutGapParameter,hX,hI,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    using hgap

/-- Original top permutations provide a faithful cover of the SAME
acting quotient, reindexed only to the literal finite point type. -/
def zeroCutTopCover [Finite I] : F.top.range →* Equiv.Perm (Fin (Nat.card I)) :=
  (Finite.equivFinOfCardEq (show Nat.card I=Nat.card I from rfl)).permCongrHom.toMonoidHom.comp
    F.top.range.subtype

theorem zeroCutTopCover_injective [Finite I] : Function.Injective F.zeroCutTopCover :=
  (Finite.equivFinOfCardEq (show Nat.card I=Nat.card I from rfl)).permCongrHom.injective.comp
    Subtype.val_injective

/-- Every power uses one complete exterior subgroup. The quotient B
need not itself have a faithful action on the prefix points. -/
theorem zeroCutMomentWeight_moment_le [Finite I] (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), F.zeroCutMomentWeight N J^q)≤
      (subgroupCount (b+q*Nat.card I) : ℝ) := by
  have h := fusionCentralPrefixWeight_moment_le F.zeroCutTopCover
    F.zeroCutTopCover_injective (F.sectionTopQuotient N)
    (F.sectionTopQuotient_surjective N) b 0 q
  simpa only [fusionCentralPrefixWeight,zeroCutMomentWeight,zero_mul,pow_zero,mul_one,
    mul_zero,add_zero] using h

/-- Arbitrary survival is tested on the original maps to U/N. Actual
Sylow kernels in each same-source fibre supply the permutation rank bound. -/
theorem zeroCut_original_survival_card_le [Finite X] [Finite I] {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b)))
    (S : GroupEpimorphism J (U ⧸ N) → Prop) :
    (Nat.card {f : GroupEpimorphism J (U ⧸ N) // S f} : ℝ)≤
      F.zeroCutLiftConstant N * (2:ℝ)^((F.zeroCutCapacity N/2)*(b:ℝ)) *
        F.zeroCutMomentWeight N J := by
  let P : ∀ β : GroupEpimorphism J (U ⧸ (F.top.ker⊔N)), Sylow 2 β.1.ker :=
    fun _ => Classical.arbitrary _
  have h := fusionEpimorphism_survival_card_le_schur_of_rank_bound 2
    (F.zeroCutBase N) (F.zeroCutBase_surjective N) (F.zeroCutModule N)
    (F.zeroCutModuleChart N) P S (b:ℝ)
    (fun β => permutationTwoGroup_sylowKernel_primeAbelianizationRank_le J β.1 (P β))
  change _≤F.zeroCutMomentWeight N J *
    (F.zeroCutLiftConstant N*(2:ℝ)^(F.zeroCutCapacity N*((b:ℝ)/2))) at h
  calc
    _ ≤ _ := h
    _ = _ := by rw [show F.zeroCutCapacity N*((b:ℝ)/2)=
      (F.zeroCutCapacity N/2)*(b:ℝ) by ring]; ring

section Physical

variable {h : ℕ} {V : Subgroup (Equiv.Perm (Fin (2*h)))}
    (G : BinaryPairFrame V I) (L : Subgroup V) [L.Normal]

/-- Exact matching with the direct-fusion local factor; the original
translation/cohomology coefficient remains outside the graph moment. -/
theorem zeroCut_localFactor_eq (b : ℕ) :
    fusionLocalFactor b h (Nat.card I) (G.zeroCutLiftConstant L) (G.zeroCutGapParameter L)=
      G.zeroCutLiftConstant L*(2:ℝ)^((G.zeroCutCapacity L/2)*(b:ℝ)) := by
  unfold fusionLocalFactor
  have he : (((2*h:ℕ):ℝ)-(Nat.card I:ℝ)-16*G.zeroCutGapParameter L)/8=
      G.zeroCutCapacity L/2 := by
    unfold zeroCutGapParameter
    rw [Nat.card_fin]
    ring
  rw [he]

theorem zeroCut_original_survivingEpiCount_le [Finite I] {b : ℕ}
    (P : Subgroup (V × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount V P ⟨L,inferInstance⟩ J≤
      fusionLocalFactor b h (Nat.card I) (G.zeroCutLiftConstant L) (G.zeroCutGapParameter L)*
        G.zeroCutMomentWeight L J := by
  rw [G.zeroCut_localFactor_eq L b]
  exact G.zeroCut_original_survival_card_le L J
    (fun f => P (fusionFullGoursatEncode ⟨L,inferInstance⟩ J f).1)

end Physical
end SymmetricSubgroupAsymptotics.BinaryPairFrame
