import SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordHeightCoordinates
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionParameterAction

/-! The actual cyclic/Frobenius action on the WORD root parameters.
All index, height and root-parameter compatibilities are discharged from
the literal fixed-section identities, before comparison with the quotient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordCoordinateTwist
open CFSGTrialityD4PositiveRootIndex CFSGTrialityD4PositiveRootOrbits
open CFSGTrialityGeckWordRootIndex CFSGTrialityGeckWordHeightCoordinates
open CFSGTrialityGeckSectionParameterAction CFSGTrialityGeckPositiveTwist
open CFSGTrialityGeckSectionRootLabels CFSGTrialityGeckSectionHeightMembership
open CFSGTrialityGeckFixedRootSections CFSGTrialityGeckMatrixTwist CFSGIntegerHeightSign

def cycleIndex : Equiv.Perm OrbitIndex :=
  Equiv.sumCongr (Equiv.refl (Fin 3)) (Equiv.prodCongr (Equiv.refl (Fin 3)) cycleEquiv)

theorem cycleIndex_height (a : OrbitIndex) :
    height (wordPositiveRoot (cycleIndex a)).val.val = height (wordPositiveRoot a).val.val := by
  rcases a with s | ⟨s,k⟩
  · rfl
  · change height (shortLabel s (cycle k)).val = height (shortLabel s k).val
    exact (short_label_height s (cycle k)).trans (short_label_height s k).symm

def heightCycle (h : ℤ) : Equiv.Perm (WordHeightIndex h) where
  toFun a := ⟨cycleIndex a.val, (cycleIndex_height a.val).trans a.property⟩
  invFun a := ⟨cycleIndex.symm a.val, by
    have he := cycleIndex_height (cycleIndex.symm a.val)
    rw [Equiv.apply_symm_apply] at he
    exact he.symm.trans a.property⟩
  left_inv a := Subtype.ext (cycleIndex.symm_apply_apply a.val)
  right_inv a := Subtype.ext (cycleIndex.apply_symm_apply a.val)

def fieldParameterAut (K : Type) [Field K] (σ : K ≃+* K) : MulAut (Multiplicative K) where
  toFun a := Multiplicative.ofAdd (σ a.toAdd)
  invFun a := Multiplicative.ofAdd (σ.symm a.toAdd)
  left_inv a := congrArg Multiplicative.ofAdd (σ.symm_apply_apply a.toAdd)
  right_inv a := congrArg Multiplicative.ofAdd (σ.apply_symm_apply a.toAdd)
  map_mul' a b := congrArg Multiplicative.ofAdd (map_add σ a.toAdd b.toAdd)

theorem wordPositiveParameter_action (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (a : OrbitIndex) (t : Multiplicative K) :
    positiveTwist K σ (wordPositiveParameterHom K a t) =
      wordPositiveParameterHom K (cycleIndex a) (fieldParameterAut K σ t) := by
  apply Subtype.ext
  rw [positiveTwist_val]
  rcases a with s | ⟨s,k⟩
  · change unitTwist K σ (longSection K s false t.toAdd) =
      longSection K s false (σ t.toAdd)
    exact longSection_action K σ s false t.toAdd
  · change unitTwist K σ (shortFactor K s k t.toAdd) =
      shortFactor K s (cycle k) (σ t.toAdd)
    exact shortFactor_action K σ s k t.toAdd

def coordinateTwist (K : Type) [Field K] (σ : K ≃+* K) (h : ℤ) :
    MulAut (WordHeightIndex h → Multiplicative K) where
  toFun c j := fieldParameterAut K σ (c ((heightCycle h).symm j))
  invFun d j := (fieldParameterAut K σ).symm (d (heightCycle h j))
  left_inv c := by
    funext j
    simp only [Equiv.symm_apply_apply, MulEquiv.symm_apply_apply]
  right_inv d := by
    funext j
    simp only [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  map_mul' c d := by
    funext j
    exact map_mul (fieldParameterAut K σ) _ _

theorem coordinateTwist_mulSingle (K : Type) [Field K] (σ : K ≃+* K)
    (h : ℤ) (j : WordHeightIndex h) (t : Multiplicative K) :
    coordinateTwist K σ h (Pi.mulSingle j t) =
      Pi.mulSingle (heightCycle h j) (fieldParameterAut K σ t) := by
  funext k
  change fieldParameterAut K σ
    ((Pi.mulSingle j t : WordHeightIndex h → Multiplicative K) ((heightCycle h).symm k)) =
      (Pi.mulSingle (heightCycle h j) (fieldParameterAut K σ t) :
        WordHeightIndex h → Multiplicative K) k
  by_cases hk : k = heightCycle h j
  · subst k
    rw [Equiv.symm_apply_apply]
    simp [Pi.mulSingle_apply]
  · have hn : (heightCycle h).symm k ≠ j := by
      intro he
      apply hk
      calc
        k = heightCycle h ((heightCycle h).symm k) := ((heightCycle h).apply_symm_apply k).symm
        _ = heightCycle h j := congrArg (heightCycle h) he
    simp [Pi.mulSingle_apply, hk, hn, Ne.symm hk, Ne.symm hn]

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckWordCoordinateTwist
