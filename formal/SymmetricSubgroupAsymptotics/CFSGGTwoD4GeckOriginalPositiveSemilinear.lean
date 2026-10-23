import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPairNormalizerScalars
import SymmetricSubgroupAsymptotics.CFSGRootParameterScalarNormalizer

/-! Actual positive simple-chart maps are scalar times field automorphisms.
Both scalar bounds and complete realization are proved for the same
original opposed-pair normalizer. Field coupling remains a later step. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPositiveSemilinear
open CFSGGTwoD4GeckOriginalSimpleStabilizer CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckOriginalPairNormalizer CFSGGTwoD4GeckPairNormalizerScalars
open CFSGRootParameterAutomorphism CFSGRootParameterScalarNormalizer
open CFSGFiniteFieldScalarNormalizer CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

theorem positive_parameters_semilinear (f : simpleStabilizer K p) :
    ∃ (c : Bool → Kˣ) (tau : Bool → RingAut K), ∀ (a : Bool) (t : K),
      simpleStabilizerAction K p f (originalSimpleHom K false a (Multiplicative.ofAdd t)) =
        originalSimpleHom K false a (Multiplicative.ofAdd ((c a : K)*tau a t)) := by
  classical
  let F := simpleStabilizerAction K p f
  have hT : (originalPairNormalizer K p).map F.toMonoidHom = originalPairNormalizer K p :=
    originalPairNormalizer_map K p F
      (pair_preserves_positive K p f.val) (pair_preserves_negative K p f.val)
  have haxis (a : Bool) : ∃ (c : Kˣ) (tau : RingAut K), ∀ t : K,
      F (originalSimpleHom K false a (Multiplicative.ofAdd t)) =
        originalSimpleHom K false a (Multiplicative.ofAdd ((c : K)*tau t)) := by
    let X := originalSimpleHom K false a
    have hX : X.range.map F.toMonoidHom = X.range := simple_preserves_chart K p f false a
    have hx := originalSimpleHom_injective K false a
    have hnorm := parameterAut_mem_scalar_normalizer X hx F hX (originalPairNormalizer K p)
      (by
        intro d hd
        obtain ⟨c,hc⟩ := originalPairNormalizer_positive_scalars K p d hd
        exact ⟨c a,hc a⟩)
      (by
        intro c
        obtain ⟨d,hd,hc⟩ := originalPairNormalizer_realizes_scalars K p (fun _ => c)
        exact ⟨d,hd,hc a⟩) hT
    obtain ⟨⟨c,tau⟩,htau,_⟩ := exists_unique_scalar_ringAut (parameterAut X hx F hX) hnorm
    refine ⟨c,tau,?_⟩
    intro t
    exact (parameterAut_apply X hx F hX t).symm.trans
      (congrArg (fun z => X (Multiplicative.ofAdd z)) (htau t))
  choose c tau htau using haxis
  exact ⟨c,tau,htau⟩

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPositiveSemilinear
