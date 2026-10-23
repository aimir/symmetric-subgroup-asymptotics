import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPathAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalNegativeRootAction
import SymmetricSubgroupAsymptotics.CFSGFFourE6SimpleGeneratedParameters
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalPairAlignment
import SymmetricSubgroupAsymptotics.CFSGE6GeckOppositeOrbitCommutation
import SymmetricSubgroupAsymptotics.CFSGSignedSubgroupPermutationAgreement
import SymmetricSubgroupAsymptotics.CFSGRankOneNoncommutation

/-! The positive and negative native F4 charts have the SAME path
permutation. Distinct opposite labels commute by actual E6 words;
matching labels have an original rank-one noncommutation witness.
The unoriented path and its possible reversal are retained in every
characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSignedPathAction
open CFSGFFourE6OriginalPathAction CFSGFFourE6OriginalNegativeRootAction
open CFSGFFourE6OriginalSimpleParameters CFSGFFourE6OriginalSimpleRootRanges
open CFSGFFourE6OriginalRootIntersection CFSGFFourE6OriginalPairAlignment
open CFSGFFourE6OriginalProjection CFSGFFourE6OriginalOppositeAlignment
open CFSGFFourE6SimpleGeneratedParameters CFSGFFourE6GeneratedOriginalProjection
open CFSGE6GeckFixedOrbitRootGroups CFSGE6GeckNegativeOrbitRootGroups
open CFSGE6GeckOppositeOrbitCommutation CFSGE6GeckRelativeSimpleHom
open CFSGTwistedE6GeckRelativeRootGenerated CFSGSignedSubgroupPermutationAgreement
open CFSGFourRootPathPermutation CFSG.Models.Chevalley

theorem original_distinct_opposite_commute (K : Type) [Field K] [Finite K]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)] (i j : Fin 4) (hne : i≠j)
    (a b : Multiplicative K) :
    Commute (originalSimpleHom K false i a) (originalSimpleHom K true j b) := by
  have hx : foldedFixedHom K false i a∈fixedOrbitPositive K (RingEquiv.refl K) i := by
    rw [fixedOrbitPositive_native_range]
    exact ⟨a,rfl⟩
  have hy : foldedFixedHom K true j b∈fixedOrbitNegative K (RingEquiv.refl K) j := by
    rw [fixedOrbitNegative_native_range]
    exact ⟨b,rfl⟩
  have hc := orbit_groups_opposite_commute K i j hne
    (foldedFixedHom K false i a).val hx (foldedFixedHom K true j b).val hy
  have hJ : Commute (simpleInGenerated K false i a) (simpleInGenerated K true j b) :=
    Subtype.ext hc.eq
  simpa only [simpleInGenerated_original] using hJ.map (generatedToOriginal K)

private theorem generated_simple_reflection (K : Type) [Field K] (i : Fin 4) :
    (simpleInGenerated K false i (Multiplicative.ofAdd 1)*
      (simpleInGenerated K true i (Multiplicative.ofAdd 1))⁻¹*
      simpleInGenerated K false i (Multiplicative.ofAdd 1))*
    simpleInGenerated K false i (Multiplicative.ofAdd 1)*
    (simpleInGenerated K false i (Multiplicative.ofAdd 1)*
      (simpleInGenerated K true i (Multiplicative.ofAdd 1))⁻¹*
      simpleInGenerated K false i (Multiplicative.ofAdd 1))⁻¹=
      (simpleInGenerated K true i (Multiplicative.ofAdd 1))⁻¹ := by
  change simpleWeylInGenerated K i*simpleInGenerated K false i (Multiplicative.ofAdd 1)*
    (simpleWeylInGenerated K i)⁻¹=(simpleInGenerated K true i (Multiplicative.ofAdd 1))⁻¹
  apply Subtype.ext
  change (simpleWeylInGenerated K i).val*(simpleInGenerated K false i (Multiplicative.ofAdd 1)).val*
    (simpleWeylInGenerated K i).val⁻¹=(simpleInGenerated K true i (Multiplicative.ofAdd 1)).val⁻¹
  rw [simpleWeylInGenerated_val,simpleInGenerated_val,simpleInGenerated_val]
  exact rawOrbitHom_reflection K (RingEquiv.refl K) i

private theorem mapped_rank_one_not_commute {A B : Type*} [Group A] [Group B]
    (f : A→*B) (u v : A) (hsep : f u≠(f v)⁻¹)
    (href : (u*v⁻¹*u)*u*(u*v⁻¹*u)⁻¹=v⁻¹) : ¬Commute (f u) (f v) := by
  apply CFSGRankOneNoncommutation.not_commute _ _ hsep
  simpa only [map_mul,map_inv] using congrArg f href

theorem original_same_axis_not_commute (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (i : Fin 4) :
    ¬Commute (originalSimpleHom K false i (Multiplicative.ofAdd 1))
      (originalSimpleHom K true i (Multiplicative.ofAdd 1)) := by
  have hnonzero : originalSimpleHom K false i (Multiplicative.ofAdd 1)≠1 := by
    intro he
    have hh := originalSimpleHom_injective K p false i (he.trans (map_one _).symm)
    exact (one_ne_zero : (1:K)≠0) (congrArg (fun z : Multiplicative K=>z.toAdd) hh)
  have hU : originalSimpleHom K false i (Multiplicative.ofAdd 1)∈
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)) := by
    apply (inf_le_left : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K))⊓
      originalOppositeParabolic K i≤_)
    rw [original_positive_inf_oppositeParabolic K p,originalOrbitRoot_eq_simple_range]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  have hV : originalSimpleHom K true i (Multiplicative.ofAdd 1)∈originalNegative K := by
    apply (inf_le_left : originalNegative K⊓
      CFSGFFourE6OriginalMinimalParabolics.originalSimpleParabolic K i≤_)
    rw [original_negative_inf_simpleParabolic K p]
    exact ⟨Multiplicative.ofAdd 1,rfl⟩
  have hsep : originalSimpleHom K false i (Multiplicative.ofAdd 1)≠
      (originalSimpleHom K true i (Multiplicative.ofAdd 1))⁻¹ := by
    intro he
    obtain ⟨S,hS,hdisj⟩ := original_negative_is_sylow K p
    rw [hS] at hdisj
    have hm : originalSimpleHom K false i (Multiplicative.ofAdd 1)∈
        (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K))⊓originalNegative K :=
      ⟨hU,by rw [he];exact (originalNegative K).inv_mem hV⟩
    rw [hdisj,Subgroup.mem_bot] at hm
    exact hnonzero hm
  have hsep' : generatedToOriginal K (simpleInGenerated K false i (Multiplicative.ofAdd 1))≠
      (generatedToOriginal K (simpleInGenerated K true i (Multiplicative.ofAdd 1)))⁻¹ := by
    simpa only [simpleInGenerated_original] using hsep
  have hc := mapped_rank_one_not_commute (generatedToOriginal K)
    (simpleInGenerated K false i (Multiplicative.ofAdd 1))
    (simpleInGenerated K true i (Multiplicative.ofAdd 1)) hsep' (generated_simple_reflection K i)
  simpa only [simpleInGenerated_original] using hc

theorem exists_original_signed_path_permutation (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.F₄ K)]
    (f : MulAut (Projective CartanMatrix.F₄ K))
    (hU : (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)).map f.toMonoidHom=
      (originalPositiveSylow K p : Subgroup (Projective CartanMatrix.F₄ K)))
    (hV : (originalNegative K).map f.toMonoidHom=originalNegative K) :
    ∃sigma : pathAut,∀neg : Bool,∀i : Fin 4,
      (originalSimpleHom K neg i).range.map f.toMonoidHom=
        (originalSimpleHom K neg (sigma.val i)).range := by
  obtain ⟨sigma,hpos⟩ := exists_original_path_permutation K p f hU hV
  obtain ⟨tau,hneg⟩ := exists_original_negative_root_permutation K p f hU hV
  have hpos' (i : Fin 4) : (originalSimpleHom K false i).range.map f.toMonoidHom=
      (originalSimpleHom K false (sigma.val i)).range := by
    simpa only [originalOrbitRoot_eq_simple_range] using hpos i
  have he : sigma.val=tau := permutations_agree
    (fun i=>(originalSimpleHom K false i).range) (fun i=>(originalSimpleHom K true i).range)
    (by
      rintro i j hij _ ⟨a,rfl⟩ _ ⟨b,rfl⟩
      exact original_distinct_opposite_commute K i j hij a b)
    (fun i=>⟨_,⟨Multiplicative.ofAdd 1,rfl⟩,_,⟨Multiplicative.ofAdd 1,rfl⟩,
      original_same_axis_not_commute K p i⟩) f sigma.val tau hpos' hneg
  refine ⟨sigma,fun neg i=>?_⟩
  cases neg
  · exact hpos' i
  · rw [he]
    exact hneg i

end SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSignedPathAction
