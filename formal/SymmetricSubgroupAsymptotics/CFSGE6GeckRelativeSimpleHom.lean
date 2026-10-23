import SymmetricSubgroupAsymptotics.CFSGE6GeckSimpleChartWeyl

/-! A uniform raw parameter hom for the four folded simple labels.
At parameter one it lies in the actual fixed group for every field
endomorphism. Its rank-one word and sign-reversing conjugation are
literal identities, including both orthogonal factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeSimpleHom
open CFSGE6GeckSimpleChartWeyl CFSGE6GeckSignedSimpleParameters
open CFSGE6GeckFixedOrbitRootGroups CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6RelativeWeylOrbits
open CFSGTwistedE6FixedA2 CFSGTwistedE6PairedFixedRoots CFSGSerreQuadraticWeylWord

def rawOrbitHom (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool) (a : Fin 4) :
    Multiplicative K→*(Matrix GeckIndex GeckIndex K)ˣ :=
  ![rawPairedHom K sigma neg 0,rawPairedHom K sigma neg 1,
    rawSingletonHom K neg 1,rawSingletonHom K neg 0] a

theorem rawOrbitHom_one_parameter (K : Type) [Field K] (sigma : K≃+*K)
    (neg : Bool) (a : Fin 4) :
    rawOrbitHom K sigma neg a (Multiplicative.ofAdd 1)=orbitParameter K neg a 1 := by
  fin_cases a <;>
    simp [rawOrbitHom,rawPairedHom,rawSingletonHom,rawSimpleHom,orbitParameter,
      pairedNode,pairedPartner,node,CFSG.Models.e6Twist]

theorem rawOrbitHom_neg_one_parameter (K : Type) [Field K] (sigma : K≃+*K)
    (neg : Bool) (a : Fin 4) :
    rawOrbitHom K sigma neg a (Multiplicative.ofAdd (-1))=orbitParameter K neg a (-1) := by
  fin_cases a <;>
    simp [rawOrbitHom,rawPairedHom,rawSingletonHom,rawSimpleHom,orbitParameter,
      pairedNode,pairedPartner,node,CFSG.Models.e6Twist]

theorem rawOrbitHom_word (K : Type) [Field K] (sigma : K≃+*K) (a : Fin 4) :
    canonicalWord rawData K (orbitWord a)=
      rawOrbitHom K sigma false a (Multiplicative.ofAdd 1)*
      (rawOrbitHom K sigma true a (Multiplicative.ofAdd 1))⁻¹*
      rawOrbitHom K sigma false a (Multiplicative.ofAdd 1) := by
  have hinv : (rawOrbitHom K sigma true a (Multiplicative.ofAdd 1))⁻¹=
      rawOrbitHom K sigma true a (Multiplicative.ofAdd (-1)) :=
    (map_inv (rawOrbitHom K sigma true a) (Multiplicative.ofAdd 1)).symm
  rw [hinv,rawOrbitHom_one_parameter,rawOrbitHom_neg_one_parameter]
  exact orbit_word_parameter K a

theorem rawOrbitHom_reflection (K : Type) [Field K] (sigma : K≃+*K) (a : Fin 4) :
    canonicalWord rawData K (orbitWord a)*rawOrbitHom K sigma false a (Multiplicative.ofAdd 1)*
      (canonicalWord rawData K (orbitWord a))⁻¹=
        (rawOrbitHom K sigma true a (Multiplicative.ofAdd 1))⁻¹ := by
  have hinv : (rawOrbitHom K sigma true a (Multiplicative.ofAdd 1))⁻¹=
      rawOrbitHom K sigma true a (Multiplicative.ofAdd (-1)) :=
    (map_inv (rawOrbitHom K sigma true a) (Multiplicative.ofAdd 1)).symm
  rw [hinv]
  have hp (j : Fin 2) := paired_word_conjugates K sigma j 1
  have hs (j : Fin 2) := singleton_word_conjugates K j 1
  fin_cases a
  · exact hp 0
  · exact hp 1
  · exact hs 1
  · exact hs 0

end SymmetricSubgroupAsymptotics.CFSGE6GeckRelativeSimpleHom
