import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalNegativeStability
import SymmetricSubgroupAsymptotics.CFSGConjugateComap

/-! The retained original diagonal part is intrinsically the intersection
of the two original positive/opposite normalizers. The proved positive
normalizer reflection is transported by actual opposition. Consequently
Ree T preserves this diagonal part, with no torus recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalStability
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourOriginalAutomorphism CFSGReeFFourOriginalPositiveNormalizer
open CFSGReeFFourOriginalNegativeStability CFSGReeFFourAmbientPositiveStability
open CFSGReeFFourRelativeOpposition CFSGReeFFourOppositionFixedPositiveNegative
open CFSGFFourOriginalBruhatCells CFSGFFourOriginalAmbientHom CFSGFFourOriginalMiddleWords
open CFSGTwistedE6GeckPositiveTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGConjugateComap

private theorem conjugate_normalizer_comap {G H : Type*} [Group G] [Group H]
    (f : G→*H) (P Q : Subgroup H) (g : G)
    (hPQ : P.map (MulAut.conj (f g)).toMonoidHom=Q)
    (hP : (Subgroup.normalizer (P : Set H)).comap f=
      Subgroup.normalizer (P.comap f : Set G)) :
    (Subgroup.normalizer (Q : Set H)).comap f=
      Subgroup.normalizer (Q.comap f : Set G) := by
  have hmap := (Subgroup.map_equiv_normalizer_eq P (MulAut.conj (f g))).trans
    (congrArg (fun S : Subgroup H=>Subgroup.normalizer (S : Set H)) hPQ)
  have hsource : (P.comap f).map (MulAut.conj g).toMonoidHom=Q.comap f :=
    (comap_conjugate f P g).symm.trans (congrArg (fun S : Subgroup H=>S.comap f) hPQ)
  calc
    _=((Subgroup.normalizer (P : Set H)).map (MulAut.conj (f g)).toMonoidHom).comap f :=
      congrArg (fun S : Subgroup H=>S.comap f) hmap.symm
    _=((Subgroup.normalizer (P : Set H)).comap f).map (MulAut.conj g).toMonoidHom :=
      comap_conjugate f _ g
    _=(Subgroup.normalizer (P.comap f : Set G)).map (MulAut.conj g).toMonoidHom :=
      congrArg (fun S : Subgroup G=>S.map (MulAut.conj g).toMonoidHom) hP
    _=Subgroup.normalizer ((P.comap f).map (MulAut.conj g).toMonoidHom : Set G) :=
      Subgroup.map_equiv_normalizer_eq (P.comap f) (MulAut.conj g)
    _=_ := congrArg (fun S : Subgroup G=>Subgroup.normalizer (S : Set G)) hsource

theorem modelPositive_normalizer_comap (m : ℕ) :
    (Subgroup.normalizer (Positive (Field m) : Set (Matrix GeckIndex GeckIndex (Field m))ˣ)).comap
        (rawHom (Field m))=
      Subgroup.normalizer (modelPositive (Field m) : Set (Model CartanMatrix.F₄ (Field m))) := by
  apply le_antisymm
  · exact Subgroup.le_normalizer_comap (rawHom (Field m))
  · intro g hg
    have hB : g∈modelEnvelope (Field m) := (modelEnvelope_eq_positive_normalizer m).symm.le hg
    exact hB.1

theorem modelNegative_normalizer_comap (m : ℕ) :
    (Subgroup.normalizer (Negative (Field m) : Set (Matrix GeckIndex GeckIndex (Field m))ˣ)).comap
        (rawHom (Field m))=
      Subgroup.normalizer (modelNegative m : Set (Model CartanMatrix.F₄ (Field m))) := by
  have hraw : (Positive (Field m)).map
      (MulAut.conj (rawHom (Field m) (relativeOpposition m))).toMonoidHom=Negative (Field m) := by
    rw [rawHom_relativeOpposition]
    exact ambient_positive_image_eq_negative (Field m)
  exact conjugate_normalizer_comap (rawHom (Field m)) (Positive (Field m)) (Negative (Field m))
    (relativeOpposition m) hraw (modelPositive_normalizer_comap m)

theorem modelDiagonalPart_eq_pair_normalizer (m : ℕ) :
    modelDiagonalPart (Field m)=
      Subgroup.normalizer (modelPositive (Field m) : Set (Model CartanMatrix.F₄ (Field m))) ⊓
        Subgroup.normalizer (modelNegative m : Set (Model CartanMatrix.F₄ (Field m))) := by
  ext g
  constructor
  · intro hg
    exact ⟨(modelPositive_normalizer_comap m).le hg.1.1,
      (modelNegative_normalizer_comap m).le hg.1.2⟩
  · intro hg
    have hB : g∈modelEnvelope (Field m) := (modelEnvelope_eq_positive_normalizer m).symm.le hg.1
    exact ⟨⟨(modelPositive_normalizer_comap m).symm.le hg.1,
      (modelNegative_normalizer_comap m).symm.le hg.2⟩,hB.2⟩

theorem ree_diagonal_mem (m : ℕ) (g : Model CartanMatrix.F₄ (Field m))
    (hg : g∈modelDiagonalPart (Field m)) : reeAutomorphism m g∈modelDiagonalPart (Field m) := by
  rw [modelDiagonalPart_eq_pair_normalizer] at hg ⊢
  have hP := (Subgroup.map_equiv_normalizer_eq (modelPositive (Field m)) (reeAutomorphism m)).trans
    (congrArg (fun S : Subgroup (Model CartanMatrix.F₄ (Field m))=>
      Subgroup.normalizer (S : Set (Model CartanMatrix.F₄ (Field m)))) (ree_preserves_modelPositive m))
  have hN := (Subgroup.map_equiv_normalizer_eq (modelNegative m) (reeAutomorphism m)).trans
    (congrArg (fun S : Subgroup (Model CartanMatrix.F₄ (Field m))=>
      Subgroup.normalizer (S : Set (Model CartanMatrix.F₄ (Field m)))) (ree_preserves_modelNegative m))
  exact ⟨hP.le ⟨g,hg.1,rfl⟩,hN.le ⟨g,hg.2,rfl⟩⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalDiagonalStability
