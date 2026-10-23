import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedTailCardinality

/-! Exact height-coordinate cardinality for the identity field twist.
Each long singleton and each three-root diagram orbit contributes ONE
independent K parameter. The coordinate equivalence uses the actual
fixed-section chart, not exactness of an abstract fixed-point functor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedCoordinateCardinality
open CFSGTrialityGeckFixedTailCardinality CFSGTrialityGeckFixedCoordinateDecomposition
open CFSGTrialityGeckFixedCoordinateParameters CFSGTrialityGeckWordCoordinateTwist
open CFSGTrialityGeckWordRootIndex CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityD4PositiveRootIndex CFSGTrialityGeckSectionRootLabels
variable (K : Type) [Field K] [Finite K]

abbrev Parameters (h : ℤ) := (LongAt h→K) × (ShortAt h→K)

def coordinates (h : ℤ) (p : Parameters K h) : WordHeightIndex h→Multiplicative K
  | ⟨Sum.inl s,hj⟩ => Multiplicative.ofAdd (p.1 ⟨s,(long_height s).symm.trans hj⟩)
  | ⟨Sum.inr (s,k),hj⟩ => Multiplicative.ofAdd (p.2 ⟨s,(short_label_height s k).symm.trans hj⟩)

theorem coordinates_long (h : ℤ) (p : Parameters K h)
    (s : Fin 3) (hs : ![(1:ℤ),4,5] s=h) :
    coordinates K h p (longHeightIndex s hs)=Multiplicative.ofAdd (p.1 ⟨s,hs⟩) := rfl

theorem coordinates_short (h : ℤ) (p : Parameters K h)
    (s k : Fin 3) (hs : ![(1:ℤ),2,3] s=h) :
    coordinates K h p (shortHeightIndex s k hs)=Multiplicative.ofAdd (p.2 ⟨s,hs⟩) := rfl

theorem coordinates_step (h : ℤ) (p : Parameters K h) (j : WordHeightIndex h) :
    coordinates K h p (heightCycle h j)=
      fieldParameterAut K (RingEquiv.refl K) (coordinates K h p j) := by
  rcases j with ⟨s|⟨s,k⟩,hj⟩
  · have hs : ![(1:ℤ),4,5] s=h := (long_height s).symm.trans hj
    have he : (⟨Sum.inl s,hj⟩ : WordHeightIndex h)=longHeightIndex s hs := Subtype.ext rfl
    rw [he,heightCycle_long,coordinates_long]
    rfl
  · have hs : ![(1:ℤ),2,3] s=h := (short_label_height s k).symm.trans hj
    have he : (⟨Sum.inr (s,k),hj⟩ : WordHeightIndex h)=shortHeightIndex s k hs := Subtype.ext rfl
    rw [he,heightCycle_short,coordinates_short,coordinates_short]
    rfl

theorem coordinates_fixed (h : ℤ) (p : Parameters K h) :
    coordinateTwist K (RingEquiv.refl K) h (coordinates K h p)=coordinates K h p := by
  funext j
  have he := coordinates_step K h p ((heightCycle h).symm j)
  rw [Equiv.apply_symm_apply] at he
  exact he.symm

def parameterEquiv (h : ℤ) :
    fixedCoordinates K (RingEquiv.refl K) h≃Parameters K h where
  toFun c := (fun s=>(c.val (longHeightIndex s.val s.property)).toAdd,
    fun s=>(c.val (shortHeightIndex s.val 0 s.property)).toAdd)
  invFun p := ⟨coordinates K h p,coordinates_fixed K h p⟩
  left_inv c := by
    apply Subtype.ext
    funext j
    dsimp only
    rcases j with ⟨s|⟨s,k⟩,hj⟩
    · have hs : ![(1:ℤ),4,5] s=h := (long_height s).symm.trans hj
      have he : (⟨Sum.inl s,hj⟩ : WordHeightIndex h)=longHeightIndex s hs := Subtype.ext rfl
      rw [he,coordinates_long]
      rfl
    · have hs : ![(1:ℤ),2,3] s=h := (short_label_height s k).symm.trans hj
      have he : (⟨Sum.inr (s,k),hj⟩ : WordHeightIndex h)=shortHeightIndex s k hs := Subtype.ext rfl
      rw [he,coordinates_short]
      apply (Multiplicative.toAdd : Multiplicative K≃K).injective
      have hf := fixed_short_parameters K (RingEquiv.refl K) h c.val c.property s hs k
      fin_cases k <;> exact hf.symm
  right_inv p := by
    apply Prod.ext
    · funext s
      rfl
    · funext s
      rfl

theorem fixedCoordinates_card (h : ℤ) :
    Nat.card (fixedCoordinates K (RingEquiv.refl K) h)=
      Nat.card K ^ (Nat.card (LongAt h)+Nat.card (ShortAt h)) := by
  rw [Nat.card_congr (parameterEquiv K h)]
  simp only [Parameters,Nat.card_prod,Nat.card_fun,←pow_add]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckFixedCoordinateCardinality
