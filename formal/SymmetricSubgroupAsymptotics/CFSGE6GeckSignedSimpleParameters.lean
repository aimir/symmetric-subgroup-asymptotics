import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPairedA2Commutator
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckMatrixTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckPositiveTwist
import SymmetricSubgroupAsymptotics.CFSGTwistedE6PairedFixedRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLeadingHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOpposition

/-! Shared literal signed singleton/paired E6 simple-root parameters.
The paired parameter is injective by an ACTUAL ambient leading coordinate,
not by a four-dimensional abelianization assertion for the folded group.
Opposition proves the negative-sign assertions in every characteristic.
Twist-fixed membership is proved from its displayed parameter condition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6PairedFixedRoots CFSGTwistedE6FixedA2
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGNormTwoGeckOrthogonalWeyl
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoGeckFieldOpposition
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

abbrev pairedPartner (i : Fin 2) : Fin 6 := CFSG.Models.e6Twist (pairedNode i)

theorem paired_nodes_distinct (i : Fin 2) : pairedNode i≠pairedPartner i := by
  fin_cases i <;> decide

def rawSimpleHom (K : Type) [Field K] (neg : Bool) (j : Fin 6) :
    Multiplicative K→*(Matrix GeckIndex GeckIndex K)ˣ where
  toFun a := canonicalRoot rawData K neg j a.toAdd
  map_one' := canonicalRoot_zero rawData K neg j
  map_mul' a b := (canonicalRoot_add rawData K neg j a.toAdd b.toAdd).symm

def rawSingletonHom (K : Type) [Field K] (neg : Bool) (j : Fin 2) :
    Multiplicative K→*(Matrix GeckIndex GeckIndex K)ˣ := rawSimpleHom K neg (node j)

def rawPairedHom (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool) (j : Fin 2) :
    Multiplicative K→*(Matrix GeckIndex GeckIndex K)ˣ where
  toFun a := canonicalRoot rawData K neg (pairedNode j) a.toAdd*
    canonicalRoot rawData K neg (pairedPartner j) (sigma a.toAdd)
  map_one' := by
    change canonicalRoot rawData K neg (pairedNode j) 0*
      canonicalRoot rawData K neg (pairedPartner j) (sigma 0)=1
    rw [map_zero,canonicalRoot_zero,canonicalRoot_zero,one_mul]
  map_mul' a b := by
    change canonicalRoot rawData K neg (pairedNode j) (a.toAdd+b.toAdd)*
      canonicalRoot rawData K neg (pairedPartner j) (sigma (a.toAdd+b.toAdd))=_
    rw [map_add,←canonicalRoot_add,←canonicalRoot_add]
    exact (orthogonal_signed_roots A hs hp E6Base E6Index K
      (pairedNode j) (pairedPartner j) (by rw [E6_cartan];exact pairedNode_cartan j)
      neg neg b.toAdd (sigma a.toAdd)).mul_mul_mul_comm _ _

private def positiveRootAt (K : Type) [Field K] (i : Fin 6) (a : K) : Positive K :=
  positiveRoot A hd hs hp ho K i a

private def ambientLeading (K : Type) [Field K] : Positive K→*Multiplicative (Fin 6→K) :=
  leadingHom A hd hs hp ho K

private theorem ambientLeading_root (K : Type) [Field K] (i : Fin 6) (a : K) :
    ambientLeading K (positiveRootAt K i a)=Multiplicative.ofAdd (Pi.single i a : Fin 6→K) :=
  leadingHom_positiveRoot A hd hs hp ho K i a

theorem rawSimple_positive_injective (K : Type) [Field K] (j : Fin 6) :
    Function.Injective (rawSimpleHom K false j) := by
  intro a b he
  have hx : positiveRootAt K j a.toAdd=positiveRootAt K j b.toAdd := Subtype.ext he
  have hh := congrArg (ambientLeading K) hx
  rw [ambientLeading_root,ambientLeading_root] at hh
  have hv := congrArg (fun z : Multiplicative (Fin 6→K)=>z.toAdd j) hh
  change a.toAdd=b.toAdd
  simpa [Pi.single_apply] using hv

theorem rawPaired_positive_injective (K : Type) [Field K] (sigma : K≃+*K) (j : Fin 2) :
    Function.Injective (rawPairedHom K sigma false j) := by
  intro a b he
  have hx : positiveRootAt K (pairedNode j) a.toAdd*
      positiveRootAt K (pairedPartner j) (sigma a.toAdd)=
    positiveRootAt K (pairedNode j) b.toAdd*
      positiveRootAt K (pairedPartner j) (sigma b.toAdd) := Subtype.ext he
  have hh := congrArg (ambientLeading K) hx
  rw [map_mul,map_mul,ambientLeading_root,ambientLeading_root,
    ambientLeading_root,ambientLeading_root] at hh
  have hv := congrArg (fun z : Multiplicative (Fin 6→K)=>z.toAdd (pairedNode j)) hh
  change a.toAdd=b.toAdd
  simpa [Pi.single_apply,paired_nodes_distinct j,Ne.symm (paired_nodes_distinct j)] using hv

def rawOpposition (K : Type) [Field K] : MulAut ((Matrix GeckIndex GeckIndex K)ˣ) :=
  MulAut.conj (oppositionUnit A hs hp E6Base K)

theorem rawSimple_opposition (K : Type) [Field K] (neg : Bool) (j : Fin 6)
    (a : Multiplicative K) : rawOpposition K (rawSimpleHom K neg j a)=
      rawSimpleHom K (!neg) j a :=
  canonicalRoot_conjugate A hs hp E6Base E6Index K neg j a.toAdd

theorem rawPaired_opposition (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool)
    (j : Fin 2) (a : Multiplicative K) : rawOpposition K (rawPairedHom K sigma neg j a)=
      rawPairedHom K sigma (!neg) j a := by
  change rawOpposition K (rawSimpleHom K neg (pairedNode j) a*
    rawSimpleHom K neg (pairedPartner j) (Multiplicative.ofAdd (sigma a.toAdd)))=_
  rw [map_mul,rawSimple_opposition,rawSimple_opposition]
  rfl

theorem rawSimple_injective (K : Type) [Field K] (neg : Bool) (j : Fin 6) :
    Function.Injective (rawSimpleHom K neg j) := by
  cases neg
  · exact rawSimple_positive_injective K j
  · intro a b he
    apply rawSimple_positive_injective K j
    have hh := congrArg (rawOpposition K) he
    rw [rawSimple_opposition,rawSimple_opposition] at hh
    exact hh

theorem rawSingleton_injective (K : Type) [Field K] (neg : Bool) (j : Fin 2) :
    Function.Injective (rawSingletonHom K neg j) := rawSimple_injective K neg (node j)

theorem rawPaired_injective (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool) (j : Fin 2) :
    Function.Injective (rawPairedHom K sigma neg j) := by
  cases neg
  · exact rawPaired_positive_injective K sigma j
  · intro a b he
    apply rawPaired_positive_injective K sigma j
    have hh := congrArg (rawOpposition K) he
    rw [rawPaired_opposition,rawPaired_opposition] at hh
    exact hh

theorem rawSimple_mem_signed (K : Type) [Field K] (neg : Bool) (j : Fin 6)
    (a : Multiplicative K) : rawSimpleHom K neg j a∈SignedUpper K neg :=
  Subgroup.subset_closure ⟨(j,a.toAdd),rfl⟩

theorem rawPaired_mem_signed (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool)
    (j : Fin 2) (a : Multiplicative K) : rawPairedHom K sigma neg j a∈SignedUpper K neg :=
  (SignedUpper K neg).mul_mem (rawSimple_mem_signed K neg (pairedNode j) a)
    (rawSimple_mem_signed K neg (pairedPartner j) (Multiplicative.ofAdd (sigma a.toAdd)))

theorem rawSingleton_fixed (K : Type) [Field K] (sigma : K≃+*K) (neg : Bool)
    (j : Fin 2) (a : Multiplicative K) (ha : sigma a.toAdd=a.toAdd) :
    unitTwist K sigma (rawSingletonHom K neg j a)=rawSingletonHom K neg j a := by
  change unitTwist K sigma (canonicalRoot rawData K neg (node j) a.toAdd)=_
  rw [unitTwist_root,ha]
  have hj : CFSGSerreDiagram.e6Permutation (node j)=node j := by fin_cases j <;> decide
  rw [hj]
  rfl

theorem rawPaired_fixed (K : Type) [Field K] (sigma : K≃+*K)
    (hsigma : Function.Involutive sigma) (neg : Bool) (j : Fin 2) (a : Multiplicative K) :
    unitTwist K sigma (rawPairedHom K sigma neg j a)=rawPairedHom K sigma neg j a := by
  change unitTwist K sigma (canonicalRoot rawData K neg (pairedNode j) a.toAdd*
    canonicalRoot rawData K neg (pairedPartner j) (sigma a.toAdd))=_
  rw [map_mul,unitTwist_root,unitTwist_root]
  simp only [CFSGSerreDiagram.e6Permutation_apply,pairedPartner,pairedNode_orbit_two]
  change canonicalRoot rawData K neg (pairedPartner j) (sigma a.toAdd)*
    canonicalRoot rawData K neg (pairedNode j) (sigma (sigma a.toAdd))=
      canonicalRoot rawData K neg (pairedNode j) a.toAdd*
        canonicalRoot rawData K neg (pairedPartner j) (sigma a.toAdd)
  rw [hsigma a.toAdd]
  exact (orthogonal_signed_roots A hs hp E6Base E6Index K (pairedNode j)
    (pairedPartner j) (by rw [E6_cartan];exact pairedNode_cartan j)
      neg neg a.toAdd (sigma a.toAdd)).eq.symm

end SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters
