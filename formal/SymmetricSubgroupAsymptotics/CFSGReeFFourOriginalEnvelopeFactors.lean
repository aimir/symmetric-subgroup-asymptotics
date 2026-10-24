import SymmetricSubgroupAsymptotics.CFSGFFourOriginalPositiveDiagramImage
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalStability
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCentralTwistedCellFactors

/-! Actual original envelope elements factor uniquely into an original
positive factor and the retained diagonal part. The ambient factors first
descend through the proved ordinary diagram-fixed image correspondence.
For Ree-fixed inputs, actual T-stability and uniqueness then make both
original factors fixed. No ordinary F4 simplicity or D=T is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalEnvelopeFactors
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGFFourOriginalPositiveDiagramImage CFSGReeFFourOriginalDiagonalStability
open CFSGFFourOriginalBruhatCells CFSGFFourOriginalAmbientHom CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckMatrixTwist
open CFSGTwistedE6GeckSourceAction CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckCentralTwistedCellFactors CFSGReeFFourAmbientPositiveStability

theorem exists_model_envelope_factors (K : Type) [_root_.Field K] [Finite K] [CharP K 2]
    (b : Model CartanMatrix.F₄ K) (hb : b∈modelEnvelope K) :
    ∃u∈modelPositive K,∃d∈modelDiagonalPart K,b=u*d := by
  have ht : unitTwist K (RingEquiv.refl K) (rawHom K b)=
      (1 : MatrixGroup K).val*rawHom K b := by
    change unitTwist K (RingEquiv.refl K) (rawHom K b)=1*rawHom K b
    rw [one_mul]
    exact rawHom_diagram_fixed K b
  obtain ⟨uraw,hu,hufix,draw,hd,_hdfix,hprod⟩ := exists_central_twisted_envelope_factors
    K (RingEquiv.refl K) (rawHom K b) hb (1 : MatrixGroup K) (Subgroup.one_mem _) ht
  obtain ⟨u,huM,hrawu⟩ := exists_modelPositive_of_diagram_fixed K uraw hu hufix
  let d := u⁻¹*b
  have hrawd : rawHom K d=draw := by
    simp only [d,map_mul,map_inv,hrawu,hprod]
    group
  refine ⟨u,huM,d,?_,?_⟩
  · change rawHom K d∈CFSGTwistedE6GeckNormalizerEnvelope.diagonalNormalizer K
    rw [hrawd]
    exact hd
  · dsimp only [d]
    group

theorem model_positive_diagonal_factors_injective (K : Type) [_root_.Field K] [Finite K]
    [CharP K 2] :
    Function.Injective (fun z : modelPositive K × modelDiagonalPart K=>z.1.val*z.2.val) := by
  rintro ⟨u,d⟩ ⟨v,e⟩ he
  have hraw : rawHom K u.val*rawHom K d.val=rawHom K v.val*rawHom K e.val := by
    simpa only [map_mul] using congrArg (rawHom K) he
  have hi := positive_diagonalNormalizer_factors_injective K
    (a₁ := (⟨rawHom K u.val,u.property⟩,⟨rawHom K d.val,d.property⟩))
    (a₂ := (⟨rawHom K v.val,v.property⟩,⟨rawHom K e.val,e.property⟩)) hraw
  apply Prod.ext
  · apply Subtype.ext
    apply rawHom_injective K
    exact congrArg (fun z : Positive K × diagonalPart K=>z.1.val) hi
  · apply Subtype.ext
    apply rawHom_injective K
    exact congrArg (fun z : Positive K × diagonalPart K=>z.2.val) hi

theorem exists_fixed_model_envelope_factors (m : ℕ) (b : Model CartanMatrix.F₄ (Field m))
    (hb : b∈modelEnvelope (Field m)) (hfix : reeAutomorphism m b=b) :
    ∃u∈modelPositive (Field m),reeAutomorphism m u=u ∧
      ∃d∈modelDiagonalPart (Field m),reeAutomorphism m d=d ∧ b=u*d := by
  obtain ⟨u,hu,d,hd,hprod⟩ := exists_model_envelope_factors (Field m) b hb
  have hut : reeAutomorphism m u∈modelPositive (Field m) := by
    have h : reeAutomorphism m u∈(modelPositive (Field m)).map (reeAutomorphism m).toMonoidHom :=
      ⟨u,hu,rfl⟩
    rwa [ree_preserves_modelPositive] at h
  have hdt := ree_diagonal_mem m d hd
  have he : reeAutomorphism m u*reeAutomorphism m d=u*d := by
    have h := hfix
    rw [hprod,map_mul] at h
    exact h
  have hi := model_positive_diagonal_factors_injective (Field m)
    (a₁ := (⟨reeAutomorphism m u,hut⟩,⟨reeAutomorphism m d,hdt⟩))
    (a₂ := (⟨u,hu⟩,⟨d,hd⟩)) he
  have hufix := congrArg (fun z : modelPositive (Field m) × modelDiagonalPart (Field m)=>z.1.val) hi
  have hdfix := congrArg (fun z : modelPositive (Field m) × modelDiagonalPart (Field m)=>z.2.val) hi
  exact ⟨u,hu,hufix,d,hd,hdfix,hprod⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalEnvelopeFactors
