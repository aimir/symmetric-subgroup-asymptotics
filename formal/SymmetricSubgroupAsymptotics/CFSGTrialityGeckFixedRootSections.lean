import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootWords

/-! Explicit fixed sections for the three short and three long triality
orbits, transported by the actual fixed relative Weyl words. These are
genuine fixed matrices; their full height-quotient range is proved later. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootSections
open CFSGTrialityGeckDiagramCovariance CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckRootSubgroupTwist CFSGTrialityGeckFixedRootWords
open CFSGSerreQuadraticMatrix CFSGSerreOrdinaryTwists

def shortTransport (K : Type) [CommRing K] (s : Fin 3) :=
  ![1, longWeyl K, shortWeyl K * longWeyl K] s

def longTransport (K : Type) [CommRing K] (s : Fin 3) :=
  ![1, shortWeyl K, longWeyl K * shortWeyl K] s

theorem shortTransport_fixed (K : Type) [CommRing K] (σ : K ≃+* K) (s : Fin 3) :
    unitTwist K σ (shortTransport K s) = shortTransport K s := by
  fin_cases s
  · exact map_one _
  · exact longWeyl_fixed K σ
  · change unitTwist K σ (shortWeyl K * longWeyl K) = shortWeyl K * longWeyl K
    rw [map_mul, shortWeyl_fixed, longWeyl_fixed]

theorem longTransport_fixed (K : Type) [CommRing K] (σ : K ≃+* K) (s : Fin 3) :
    unitTwist K σ (longTransport K s) = longTransport K s := by
  fin_cases s
  · exact map_one _
  · exact shortWeyl_fixed K σ
  · change unitTwist K σ (longWeyl K * shortWeyl K) = longWeyl K * shortWeyl K
    rw [map_mul, longWeyl_fixed, shortWeyl_fixed]

def shortSection (K : Type) [CommRing K] (σ : K ≃+* K)
    (s : Fin 3) (neg : Bool) (t : K) :=
  shortTransport K s * shortOrbit K σ neg t * (shortTransport K s)⁻¹

def longSection (K : Type) [CommRing K] (s : Fin 3) (neg : Bool) (t : K) :=
  longTransport K s * canonicalRoot rawData K neg 1 t * (longTransport K s)⁻¹

theorem shortSection_fixed (K : Type) [CommRing K] (σ : K ≃+* K)
    (s : Fin 3) (neg : Bool) (t : K) (ht : σ (σ (σ t)) = t) :
    unitTwist K σ (shortSection K σ s neg t) = shortSection K σ s neg t := by
  simp only [shortSection, map_mul, map_inv, shortTransport_fixed,
    shortOrbit_fixed K σ neg t ht]

theorem longSection_fixed (K : Type) [CommRing K] (σ : K ≃+* K)
    (s : Fin 3) (neg : Bool) (t : K) (ht : σ t = t) :
    unitTwist K σ (longSection K s neg t) = longSection K s neg t := by
  have hr : unitTwist K σ (canonicalRoot rawData K neg 1 t) =
      canonicalRoot rawData K neg 1 t := by
    rw [unitTwist_raw_root, ht]
    rfl
  simp only [longSection, map_mul, map_inv, longTransport_fixed, hr]

theorem actual_shortSection_fixed (q : CFSG.PrimePower)
    (s : Fin 3) (neg : Bool) (t : q.Extension 3) :
    unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (shortSection (q.Extension 3) (definingFieldAutomorphism q 3) s neg t) =
        shortSection (q.Extension 3) (definingFieldAutomorphism q 3) s neg t :=
  shortSection_fixed _ _ s neg t
    (CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q t)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootSections
