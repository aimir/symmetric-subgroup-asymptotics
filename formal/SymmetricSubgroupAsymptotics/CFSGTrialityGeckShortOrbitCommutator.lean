import SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortTorusConjugation
import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticRootSubgroup
import Mathlib.GroupTheory.Commutator.Basic

/-! The short orbit is an actual additive root parameter subgroup.  Its
literal fixed-torus commutator has parameter t(a²-1), in every field. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator
open CFSGTrialityGeckShortTorusConjugation CFSGTrialityGeckShortParameterWeyl
open CFSGTrialityGeckFixedRootWords CFSGTrialityFixedWeylWords
open CFSGTrialityGeckDiagramCovariance CFSGSerreQuadraticMatrix

theorem shortOrbit_add (K : Type) [CommRing K] (σ : K ≃+* K) (neg : Bool) (t u : K) :
    shortOrbit K σ neg (t+u) = shortOrbit K σ neg t * shortOrbit K σ neg u := by
  let x (k : Fin 3) := canonicalRoot rawData K neg (outerNode k) (![t,σ t,σ (σ t)] k)
  let y (k : Fin 3) := canonicalRoot rawData K neg (outerNode k) (![u,σ u,σ (σ u)] k)
  have hcomm (i j : Fin 3) (hij : i ≠ j) : Commute (x i) (y j) :=
    CFSGTrialityGeckShortParameterWeyl.outer_roots_commute K i j hij neg neg _ _
  have hp : (x 0*x 1*x 2)*(y 0*y 1*y 2) =
      (x 0*y 0)*(x 1*y 1)*(x 2*y 2) := by
    calc
      _ = (x 0*x 1)*(y 0*y 1)*(x 2*y 2) :=
        ((hcomm 2 0 (by decide)).mul_right (hcomm 2 1 (by decide))).mul_mul_mul_comm _ _
      _ = _ := congrArg (fun z => z*(x 2*y 2))
        ((hcomm 1 0 (by decide)).mul_mul_mul_comm (x 0) (y 1))
  change (canonicalRoot rawData K neg 0 t * canonicalRoot rawData K neg 2 (σ t) *
      canonicalRoot rawData K neg 3 (σ (σ t))) *
      (canonicalRoot rawData K neg 0 u * canonicalRoot rawData K neg 2 (σ u) *
      canonicalRoot rawData K neg 3 (σ (σ u))) =
    (canonicalRoot rawData K neg 0 t * canonicalRoot rawData K neg 0 u) *
      (canonicalRoot rawData K neg 2 (σ t) * canonicalRoot rawData K neg 2 (σ u)) *
      (canonicalRoot rawData K neg 3 (σ (σ t)) * canonicalRoot rawData K neg 3 (σ (σ u))) at hp
  rw [canonicalRoot_add,canonicalRoot_add,canonicalRoot_add] at hp
  simpa only [shortOrbit,map_add] using hp.symm

theorem shortOrbit_zero (K : Type) [CommRing K] (σ : K ≃+* K) (neg : Bool) :
    shortOrbit K σ neg 0 = 1 := by
  simp only [shortOrbit,map_zero,canonicalRoot_zero,mul_one]

def shortOrbitHom (K : Type) [CommRing K] (σ : K ≃+* K) (neg : Bool) :
    Multiplicative K →* (Matrix GeckIndex GeckIndex K)ˣ where
  toFun t := shortOrbit K σ neg t.toAdd
  map_one' := shortOrbit_zero K σ neg
  map_mul' t u := shortOrbit_add K σ neg t.toAdd u.toAdd

theorem shortOrbit_inverse (K : Type) [CommRing K] (σ : K ≃+* K) (neg : Bool) (t : K) :
    shortOrbit K σ neg (-t) = (shortOrbit K σ neg t)⁻¹ :=
  map_inv (shortOrbitHom K σ neg) (Multiplicative.ofAdd t)

theorem short_torus_commutator (K : Type) [Field K] (σ : K ≃+* K) (a : Kˣ) (t : K) :
    ⁅shortTorusWord K σ a,shortOrbit K σ false t⁆ =
      shortOrbit K σ false (t*((a : K)^2-1)) := by
  rw [commutatorElement_def,shortTorusWord_conjugate,← shortOrbit_inverse,← shortOrbit_add]
  apply congrArg (shortOrbit K σ false)
  ring

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckShortOrbitCommutator
