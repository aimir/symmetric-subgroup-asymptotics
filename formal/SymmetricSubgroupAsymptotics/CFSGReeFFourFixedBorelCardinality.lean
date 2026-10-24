import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedDiagonalCardinality
import SymmetricSubgroupAsymptotics.CFSGReeFFourOriginalPositiveNormalizer

/-! Exact U-D coordinates of the actual original fixed upper envelope.
Both existence and uniqueness come from the checked original source
factorization, before a derived or central quotient is taken. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBorelCardinality
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFieldParameters
open CFSGFFourOriginalBruhatCells CFSGFFourOriginalAmbientHom
open CFSGReeFFourOriginalEnvelopeFactors CFSGReeFFourAmbientPositiveStability
open CFSGReeFFourOriginalPositiveNormalizer CFSGReeFFourOriginalNegativeStability
open CFSGReeFFourUniqueInversionCells CFSGReeFFourOppositionFixedPositiveNegative
open CFSGTwistedE6GeckNormalizerEnvelope CFSGReeFFourFixedAmbientHom
open CFSGReeFFourFixedPositiveCardinality CFSGReeFFourFixedDiagonalCardinality

def fixedBorel (m : ℕ) : Subgroup (originalModelFixed m) :=
  (modelEnvelope (Field m)).comap (originalModelFixed m).subtype

theorem positive_le_borel (m : ℕ) : fixedPositive m≤fixedBorel m := by
  intro u hu
  exact positive_le_envelope (Field m) hu

theorem diagonal_le_borel (m : ℕ) : fixedDiagonal m≤fixedBorel m := by
  intro d hdD
  exact diagonalNormalizer_le_envelope (Field m) hdD

theorem exists_fixed_borel_factors (m : ℕ) (b : fixedBorel m) :
    ∃u∈fixedPositive m,∃d∈fixedDiagonal m,b.val=u*d := by
  obtain ⟨u,hu,huf,d,hdD,hdf,he⟩ := exists_fixed_model_envelope_factors m
    b.val.val b.property b.val.property
  exact ⟨⟨u,huf⟩,hu,⟨d,hdf⟩,hdD,Subtype.ext he⟩

theorem fixedBorel_eq_sup (m : ℕ) : fixedBorel m=fixedPositive m⊔fixedDiagonal m := by
  apply le_antisymm
  · intro b hb
    obtain ⟨u,hu,d,hdD,he⟩ := exists_fixed_borel_factors m ⟨b,hb⟩
    change b=u*d at he
    rw [he]
    exact (fixedPositive m⊔fixedDiagonal m).mul_mem
      ((show fixedPositive m≤fixedPositive m⊔fixedDiagonal m from le_sup_left) hu)
      ((show fixedDiagonal m≤fixedPositive m⊔fixedDiagonal m from le_sup_right) hdD)
  · exact sup_le (positive_le_borel m) (diagonal_le_borel m)

def borelProduct (m : ℕ) : fixedPositive m×fixedDiagonal m → fixedBorel m := fun p=>
  ⟨p.1.val*p.2.val,(fixedBorel m).mul_mem
    (positive_le_borel m p.1.property) (diagonal_le_borel m p.2.property)⟩

theorem borelProduct_bijective (m : ℕ) : Function.Bijective (borelProduct m) := by
  constructor
  · intro p q he
    have hv := congrArg (fun b : fixedBorel m=>b.val.val) he
    change p.1.val.val*p.2.val.val=q.1.val.val*q.2.val.val at hv
    have hi := model_positive_diagonal_factors_injective (Field m)
      (a₁ := (⟨p.1.val.val,p.1.property⟩,⟨p.2.val.val,p.2.property⟩))
      (a₂ := (⟨q.1.val.val,q.1.property⟩,⟨q.2.val.val,q.2.property⟩)) hv
    apply Prod.ext
    · apply Subtype.ext
      exact Subtype.ext (congrArg (fun z : modelPositive (Field m)×modelDiagonalPart (Field m)=>z.1.val) hi)
    · apply Subtype.ext
      exact Subtype.ext (congrArg (fun z : modelPositive (Field m)×modelDiagonalPart (Field m)=>z.2.val) hi)
  · intro b
    obtain ⟨u,hu,d,hdD,he⟩ := exists_fixed_borel_factors m b
    exact ⟨(⟨u,hu⟩,⟨d,hdD⟩),Subtype.ext he.symm⟩

theorem fixedBorel_card (m : ℕ) :
    Nat.card (fixedBorel m)=(2^(2*m+1))^12*(2^(2*m+1)-1)^2 := by
  rw [←Nat.card_congr (Equiv.ofBijective (borelProduct m) (borelProduct_bijective m)),
    Nat.card_prod,fixedPositive_card,fixedDiagonal_card]

theorem fixedBorel_le_normalizer (m : ℕ) :
    fixedBorel m≤Subgroup.normalizer (fixedPositive m : Set (originalModelFixed m)) := by
  intro b hb
  have hn : b.val∈Subgroup.normalizer (modelPositive (Field m) : Set _) := by
    rw [←modelEnvelope_eq_positive_normalizer]
    exact hb
  rw [fixedPositive_eq_model_comap]
  exact Subgroup.le_normalizer_comap (originalModelFixed m).subtype hn

theorem fixedBorel_negative_disjoint (m : ℕ) : Disjoint (fixedBorel m) (fixedNegative m) := by
  apply Subgroup.disjoint_def.mpr
  intro x hb hv
  apply Subtype.ext
  exact Subgroup.disjoint_def.mp (modelEnvelope_negative_disjoint m) hb hv

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBorelCardinality
