import SymmetricSubgroupAsymptotics.CFSGE6GeckFixedUpperNormalizer
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeOpposition
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRootGeneratedPGroup

/-! The normalizer of the actual fixed negative root part inside J
lies in the ambient negative normalizer. Conjugation by the SAME fixed
relative opposition transfers the proved positive regularity argument.
Its square is not assumed to be one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGE6GeckFixedNegativeNormalizer
open CFSGE6GeckFixedUpperNormalizer CFSGTwistedE6GeckRelativeOpposition
open CFSGTwistedE6GeckRelativeRootGenerated CFSGTwistedE6GeckFixedRangePreimage
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckRootGeneratedPGroup

theorem negative_normalizer_inter_generated_le (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) :
    Subgroup.normalizer (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓
      fixedRootGenerated K sigma ≤
        Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓ MatrixGroup K := by
  intro d hd
  let e := MulAut.conj (relativeOpposition K)
  have hN : (Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)).map e.toMonoidHom=
      Subgroup.normalizer (signedFixed K sigma true : Set (Matrix GeckIndex GeckIndex K)ˣ) :=
    (Subgroup.map_equiv_normalizer_eq (signedFixed K sigma false) e).trans
      (congrArg (fun S : Subgroup ((Matrix GeckIndex GeckIndex K)ˣ)=>
        Subgroup.normalizer (S : Set ((Matrix GeckIndex GeckIndex K)ˣ)))
        (fixed_positive_image_eq_fixed_negative K sigma))
  have hdN : d∈(Subgroup.normalizer
      (signedFixed K sigma false : Set (Matrix GeckIndex GeckIndex K)ˣ)).map e.toMonoidHom :=
    hN.symm ▸ hd.1
  obtain ⟨c,hcN,he⟩ := hdN
  have hcJ : c∈fixedRootGenerated K sigma := by
    have hO := relativeOpposition_mem_generated K sigma
    have hh := (fixedRootGenerated K sigma).mul_mem
      ((fixedRootGenerated K sigma).mul_mem ((fixedRootGenerated K sigma).inv_mem hO) hd.2) hO
    have hcancel : (relativeOpposition K)⁻¹*d*relativeOpposition K=c := by
      rw [←he]
      change (relativeOpposition K)⁻¹*(relativeOpposition K*c*(relativeOpposition K)⁻¹)*
        relativeOpposition K=c
      group
    exact hcancel ▸ hh
  have hcB := fixed_upper_normalizer_inter_preimage_le K sigma
    ⟨hcN,fixedRootGenerated_le_preimage K sigma hcJ⟩
  have hn := (Positive K).le_normalizer_map e.toMonoidHom
    (show d∈(Subgroup.normalizer (Positive K : Set (Matrix GeckIndex GeckIndex K)ˣ)).map
      e.toMonoidHom from ⟨c,hcB.1.1,he⟩)
  change d∈Subgroup.normalizer ((Positive K).map
    (MulAut.conj (relativeOpposition K)).toMonoidHom : Set (Matrix GeckIndex GeckIndex K)ˣ) at hn
  rw [positive_image_eq_negative] at hn
  exact ⟨hn,fixedRootGenerated_le_matrixGroup K sigma hd.2⟩

theorem negative_normalizer_map_le (K : Type) [Field K] [Finite K] (sigma : K≃+*K) :
    (Subgroup.normalizer (rootPart K sigma true : Set (fixedRootGenerated K sigma))).map
      (fixedRootGenerated K sigma).subtype≤
        Subgroup.normalizer (Negative K : Set (Matrix GeckIndex GeckIndex K)ˣ) ⊓ MatrixGroup K := by
  have hmap : (rootPart K sigma true).map (fixedRootGenerated K sigma).subtype=
      signedFixed K sigma true :=
    Subgroup.map_subgroupOf_eq_of_le (signedFixed_le_generated K sigma true)
  rintro _ ⟨x,hx,rfl⟩
  have hn := (rootPart K sigma true).le_normalizer_map (fixedRootGenerated K sigma).subtype
    (show x.val∈(Subgroup.normalizer (rootPart K sigma true : Set (fixedRootGenerated K sigma))).map
      (fixedRootGenerated K sigma).subtype from ⟨x,hx,rfl⟩)
  rw [hmap] at hn
  exact negative_normalizer_inter_generated_le K sigma ⟨hn,x.property⟩

end SymmetricSubgroupAsymptotics.CFSGE6GeckFixedNegativeNormalizer
