import SymmetricSubgroupAsymptotics.CFSGE6GeckOrthogonalPairChart
import SymmetricSubgroupAsymptotics.CFSGFixedOrthogonalPairChart

/-! Genuine fixed points of the actual E6 singleton and paired simple
root products. The paired fixed locus is the coefficient graph b=sigma a,
using proved unrestricted-product injectivity, in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPairChart
open CFSGE6GeckOrthogonalPairChart CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2 CFSGSerreDiagram
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckOrthogonalWeyl CFSGSerreQuadraticMatrix CFSGFixedOrthogonalPairChart
local notation "A" => CartanMatrix.E₆
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite

theorem singleton_fixed_iff (K : Type) [Field K] (sigma : K≃+*K)
    (neg : Bool) (j : Fin 2) (t : K) :
    unitTwist K sigma (canonicalRoot rawData K neg (node j) t)=
      canonicalRoot rawData K neg (node j) t↔sigma t=t := by
  have hj : e6Permutation (node j)=node j := by fin_cases j <;> decide
  rw [unitTwist_root,hj]
  constructor
  · intro he
    have hh := rawSingleton_injective K neg j
      (show rawSingletonHom K neg j (Multiplicative.ofAdd (sigma t))=
        rawSingletonHom K neg j (Multiplicative.ofAdd t) from he)
    exact congrArg Multiplicative.toAdd hh
  · intro he
    rw [he]

theorem pair_product_injective (K : Type) [Field K] (neg : Bool) (j : Fin 2) :
    Function.Injective (fun p : K×K=>canonicalRoot rawData K neg (pairedNode j) p.1*
      canonicalRoot rawData K neg (pairedPartner j) p.2) := by
  intro p q he
  have hh := rawPairHom_injective K neg j
    (show rawPairHom K neg j (Multiplicative.ofAdd p.1,Multiplicative.ofAdd p.2)=
      rawPairHom K neg j (Multiplicative.ofAdd q.1,Multiplicative.ofAdd q.2) from he)
  exact Prod.ext (congrArg (fun a : Multiplicative K×Multiplicative K=>a.1.toAdd) hh)
    (congrArg (fun a : Multiplicative K×Multiplicative K=>a.2.toAdd) hh)

theorem paired_fixed_iff_graph (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (neg : Bool) (j : Fin 2) (a b : K) :
    unitTwist K sigma (canonicalRoot rawData K neg (pairedNode j) a*
      canonicalRoot rawData K neg (pairedPartner j) b)=
      canonicalRoot rawData K neg (pairedNode j) a*
        canonicalRoot rawData K neg (pairedPartner j) b↔b=sigma a := by
  apply fixed_pair_iff_graph (unitTwist K sigma).toMonoidHom sigma hsigma
    (fun t=>canonicalRoot rawData K neg (pairedNode j) t)
    (fun t=>canonicalRoot rawData K neg (pairedPartner j) t)
  · intro t u
    exact orthogonal_signed_roots A hs hp E6Base E6Index K (pairedNode j) (pairedPartner j)
      (by rw [E6_cartan];exact pairedNode_cartan j) neg neg t u
  · exact pair_product_injective K neg j
  · intro t
    change unitTwist K sigma (canonicalRoot rawData K neg (pairedNode j) t)=
      canonicalRoot rawData K neg (pairedPartner j) (sigma t)
    rw [unitTwist_root]
    rfl
  · intro t
    change unitTwist K sigma (canonicalRoot rawData K neg (pairedPartner j) t)=
      canonicalRoot rawData K neg (pairedNode j) (sigma t)
    rw [unitTwist_root]
    simp only [e6Permutation_apply,pairedPartner,pairedNode_orbit_two]

theorem exists_paired_parameter_of_fixed (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (neg : Bool) (j : Fin 2)
    (g : (Matrix GeckIndex GeckIndex K)ˣ)
    (hg : g∈canonicalRootSubgroup rawData K neg (pairedNode j)⊔
      canonicalRootSubgroup rawData K neg (pairedPartner j))
    (hfixed : unitTwist K sigma g=g) :
    ∃a : K,g=rawPairedHom K sigma neg j (Multiplicative.ofAdd a) := by
  rw [←rawPairHom_range] at hg
  obtain ⟨a,ha⟩ := hg
  have he : canonicalRoot rawData K neg (pairedNode j) a.1.toAdd*
      canonicalRoot rawData K neg (pairedPartner j) a.2.toAdd=g := ha
  have hf : unitTwist K sigma (canonicalRoot rawData K neg (pairedNode j) a.1.toAdd*
      canonicalRoot rawData K neg (pairedPartner j) a.2.toAdd)=
      canonicalRoot rawData K neg (pairedNode j) a.1.toAdd*
        canonicalRoot rawData K neg (pairedPartner j) a.2.toAdd := by
    rw [he,hfixed]
  have hb := (paired_fixed_iff_graph K sigma hsigma neg j a.1.toAdd a.2.toAdd).mp hf
  refine ⟨a.1.toAdd,?_⟩
  change g=canonicalRoot rawData K neg (pairedNode j) a.1.toAdd*
    canonicalRoot rawData K neg (pairedPartner j) (sigma a.1.toAdd)
  rw [←he,hb]

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedPairChart
