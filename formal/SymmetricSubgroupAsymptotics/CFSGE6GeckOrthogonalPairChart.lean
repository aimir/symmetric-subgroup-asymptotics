import SymmetricSubgroupAsymptotics.CFSGE6GeckSignedSimpleParameters

/-! Unrestricted two-parameter charts for the two orthogonal E6 simple
pairs. Their actual product homomorphism is injective and has range the
join of the two literal root lines, over every field and for both signs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckOrthogonalPairChart
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckDiagramCovariance
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6PairedFixedRoots
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoGeckOrthogonalWeyl CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateLeadingHom CFSGNormTwoCoordinateLeadingFactor
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

def rawPairHom (K : Type) [Field K] (neg : Bool) (j : Fin 2) :
    Multiplicative K×Multiplicative K→*(Matrix GeckIndex GeckIndex K)ˣ where
  toFun a := rawSimpleHom K neg (pairedNode j) a.1*rawSimpleHom K neg (pairedPartner j) a.2
  map_one' := by
    change rawSimpleHom K neg (pairedNode j) 1*rawSimpleHom K neg (pairedPartner j) 1=1
    rw [map_one,map_one,mul_one]
  map_mul' a b := by
    change rawSimpleHom K neg (pairedNode j) (a.1*b.1)*
      rawSimpleHom K neg (pairedPartner j) (a.2*b.2)=_
    rw [map_mul,map_mul]
    exact (orthogonal_signed_roots A hs hp E6Base E6Index K
      (pairedNode j) (pairedPartner j) (by rw [E6_cartan];exact pairedNode_cartan j)
      neg neg b.1.toAdd a.2.toAdd).mul_mul_mul_comm _ _

theorem rawPairHom_positive_injective (K : Type) [Field K] (j : Fin 2) :
    Function.Injective (rawPairHom K false j) := by
  intro a b he
  let u : Positive K := positiveRoot A hd hs hp ho K (pairedNode j) a.1.toAdd*
    positiveRoot A hd hs hp ho K (pairedPartner j) a.2.toAdd
  let v : Positive K := positiveRoot A hd hs hp ho K (pairedNode j) b.1.toAdd*
    positiveRoot A hd hs hp ho K (pairedPartner j) b.2.toAdd
  have huv : u=v := Subtype.ext he
  have hh := congrArg (leadingHom A hd hs hp ho K) huv
  dsimp only [u,v] at hh
  rw [map_mul,map_mul,leadingHom_positiveRoot,leadingHom_positiveRoot,
    leadingHom_positiveRoot,leadingHom_positiveRoot] at hh
  apply Prod.ext
  · have hc := congrArg (fun z : Multiplicative (Fin 6→K)=>z.toAdd (pairedNode j)) hh
    change a.1.toAdd=b.1.toAdd
    simpa [Pi.single_apply,paired_nodes_distinct j,Ne.symm (paired_nodes_distinct j)] using hc
  · have hc := congrArg (fun z : Multiplicative (Fin 6→K)=>z.toAdd (pairedPartner j)) hh
    change a.2.toAdd=b.2.toAdd
    simpa [Pi.single_apply,paired_nodes_distinct j,Ne.symm (paired_nodes_distinct j)] using hc

theorem rawPairHom_injective (K : Type) [Field K] (neg : Bool) (j : Fin 2) :
    Function.Injective (rawPairHom K neg j) := by
  cases neg
  · exact rawPairHom_positive_injective K j
  · intro a b he
    apply rawPairHom_positive_injective K j
    have hh := congrArg (rawOpposition K) he
    change rawOpposition K (rawSimpleHom K true (pairedNode j) a.1*
      rawSimpleHom K true (pairedPartner j) a.2)=
      rawOpposition K (rawSimpleHom K true (pairedNode j) b.1*
        rawSimpleHom K true (pairedPartner j) b.2) at hh
    rw [map_mul,map_mul,rawSimple_opposition,rawSimple_opposition,
      rawSimple_opposition,rawSimple_opposition] at hh
    exact hh

theorem rawPairHom_range (K : Type) [Field K] (neg : Bool) (j : Fin 2) :
    (rawPairHom K neg j).range=canonicalRootSubgroup rawData K neg (pairedNode j)⊔
      canonicalRootSubgroup rawData K neg (pairedPartner j) := by
  apply le_antisymm
  · rintro _ ⟨a,rfl⟩
    exact (canonicalRootSubgroup rawData K neg (pairedNode j)⊔
      canonicalRootSubgroup rawData K neg (pairedPartner j)).mul_mem
      ((show canonicalRootSubgroup rawData K neg (pairedNode j)≤
        canonicalRootSubgroup rawData K neg (pairedNode j)⊔
          canonicalRootSubgroup rawData K neg (pairedPartner j) from le_sup_left) ⟨a.1.toAdd,rfl⟩)
      ((show canonicalRootSubgroup rawData K neg (pairedPartner j)≤
        canonicalRootSubgroup rawData K neg (pairedNode j)⊔
          canonicalRootSubgroup rawData K neg (pairedPartner j) from le_sup_right) ⟨a.2.toAdd,rfl⟩)
  · apply sup_le
    · rintro _ ⟨t,rfl⟩
      refine ⟨(Multiplicative.ofAdd t,1),?_⟩
      change rawSimpleHom K neg (pairedNode j) (Multiplicative.ofAdd t)*
        rawSimpleHom K neg (pairedPartner j) 1=_
      rw [map_one,mul_one]
      rfl
    · rintro _ ⟨t,rfl⟩
      refine ⟨(1,Multiplicative.ofAdd t),?_⟩
      change rawSimpleHom K neg (pairedNode j) 1*
        rawSimpleHom K neg (pairedPartner j) (Multiplicative.ofAdd t)=_
      rw [map_one,one_mul]
      rfl

end SymmetricSubgroupAsymptotics.CFSGE6GeckOrthogonalPairChart
