import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckNormalizerEnvelopeTwist
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionFactor
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckIntegralWord

/-! The literal positive inversion subgroup and its natural inclusion.
The twist of a fixed-word inversion factor stays in the same subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckInversionParts
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckNormalizerEnvelopeTwist
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGNormTwoCoordinateWeylIntersectionFactor CFSGNormTwoCoordinateRootHeightQuotient
open CFSGSerreQuadraticWeylWord CFSGNormTwoGeckIntegralWord
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

abbrev InversionPart (K : Type) [Field K] (w : List (Fin 6)) :=
  wordSignPart A hd hs hp ho K w true

def inversionEmbedding (K : Type) [Field K] (w : List (Fin 6)) :
    InversionPart K w →* (Matrix GeckIndex GeckIndex K)ˣ :=
  (PositiveGroup A hd hs hp ho K).subtype.comp (InversionPart K w).subtype

theorem inversionEmbedding_injective (K : Type) [Field K] (w : List (Fin 6)) :
    Function.Injective (inversionEmbedding K w) := by
  intro v u he
  exact Subtype.ext (Subtype.ext he)

theorem exists_positive_inversion_factors (K : Type) [Field K] [Finite K]
    (w : List (Fin 6)) (u : Positive K) :
    ∃p : (Matrix GeckIndex GeckIndex K)ˣ,
      CFSGNormTwoGeckWeylWordDegree.wordUnit A hs hp E6Base E6Index K w*p*
        (CFSGNormTwoGeckWeylWordDegree.wordUnit A hs hp E6Base E6Index K w)⁻¹∈Positive K ∧
      ∃v : InversionPart K w,u.val=p*inversionEmbedding K w v := by
  let up : PositiveGroup A hd hs hp ho K := ⟨u.val,u.property⟩
  obtain ⟨z,hz⟩ := (word_parts_product_bijective A hd hs hp ho K w).surjective up
  let p : (Matrix GeckIndex GeckIndex K)ˣ := z.1.val.val
  let v : InversionPart K w := z.2
  have he : p*inversionEmbedding K w v=u.val :=
    congrArg (fun x : PositiveGroup A hd hs hp ho K =>
      (x.val : (Matrix GeckIndex GeckIndex K)ˣ)) hz
  refine ⟨p,?_,v,he.symm⟩
  rw [word_eq_canonicalWord]
  exact z.1.property

def inversionTwistElement (K : Type) [Field K] (sigma : K≃+*K)
    (w : List (Fin 6))
    (hW : unitTwist K sigma (CFSGNormTwoGeckWeylWordDegree.wordUnit A hs hp E6Base E6Index K w)=
      CFSGNormTwoGeckWeylWordDegree.wordUnit A hs hp E6Base E6Index K w)
    (v : InversionPart K w) : InversionPart K w := by
  have hpos : unitTwist K sigma v.val.val∈Positive K := by
    have hm : unitTwist K sigma v.val.val∈(Positive K).map (unitTwist K sigma).toMonoidHom :=
      ⟨v.val.val,v.val.property,rfl⟩
    rwa [positive_twist_map] at hm
  refine ⟨⟨unitTwist K sigma v.val.val,hpos⟩,?_⟩
  change MulAut.conj (canonicalWord rawData K w) (unitTwist K sigma v.val.val)∈Negative K
  have hw : unitTwist K sigma (canonicalWord rawData K w)=canonicalWord rawData K w := by
    simpa only [word_eq_canonicalWord] using hW
  have hn : unitTwist K sigma (MulAut.conj (canonicalWord rawData K w) v.val.val)∈Negative K := by
    have hm : unitTwist K sigma (MulAut.conj (canonicalWord rawData K w) v.val.val)∈
        (Negative K).map (unitTwist K sigma).toMonoidHom := ⟨_,v.property,rfl⟩
    rwa [signedUpper_twist_map K sigma true] at hm
  have he : unitTwist K sigma (MulAut.conj (canonicalWord rawData K w) v.val.val)=
      MulAut.conj (canonicalWord rawData K w) (unitTwist K sigma v.val.val) := by
    change unitTwist K sigma (_*_*_⁻¹)=_*_*_⁻¹
    rw [map_mul,map_mul,map_inv,hw]
  rwa [he] at hn

theorem inversionTwistElement_value (K : Type) [Field K] (sigma : K≃+*K)
    (w : List (Fin 6)) (hW) (v : InversionPart K w) :
    inversionEmbedding K w (inversionTwistElement K sigma w hW v)=
      unitTwist K sigma (inversionEmbedding K w v) := rfl

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckInversionParts
