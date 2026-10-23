import SymmetricSubgroupAsymptotics.CFSGTrialityGeckSectionQuotientCoordinates
import Mathlib.Algebra.BigOperators.Pi

/-! Every fixed coordinate vector is a product of the actual section
coordinate vectors.  Active orbits are selected by their proved heights;
no stability of an arbitrarily ordered root list is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateDecomposition
open CFSGTrialityGeckFixedCoordinateParameters CFSGTrialityGeckSectionQuotientCoordinates
open CFSGTrialityGeckWordCoordinateTwist CFSGTrialityGeckWordRootIndex
open CFSGTrialityGeckSectionRootLabels CFSGTrialityD4PositiveRootIndex

abbrev LongAt (h : ℤ) := {s : Fin 3 // ![(1 : ℤ),4,5] s = h}
abbrev ShortAt (h : ℤ) := {s : Fin 3 // ![(1 : ℤ),2,3] s = h}

private theorem long_index_injective (h : ℤ) :
    Function.Injective (fun s : LongAt h => longHeightIndex s.val s.property) := by
  intro s t he
  apply Subtype.ext
  exact Sum.inl.inj (congrArg (fun j : WordHeightIndex h => j.val) he)

private theorem short_index_first {h : ℤ} (s t : ShortAt h) (k l : Fin 3)
    (he : shortHeightIndex s.val k s.property = shortHeightIndex t.val l t.property) : s = t := by
  apply Subtype.ext
  exact congrArg Prod.fst (Sum.inr.inj (congrArg (fun j : WordHeightIndex h => j.val) he))

private theorem short_coordinates_at (K : Type) [Field K] (σ : K ≃+* K)
    {h : ℤ} (s : ShortAt h) (t : Multiplicative K) (k : Fin 3) :
    shortSectionCoordinates K σ s.val s.property t (shortHeightIndex s.val k s.property) =
      ![t,fieldParameterAut K σ t,fieldParameterAut K σ (fieldParameterAut K σ t)] k := by
  fin_cases k <;>
    simp [shortSectionCoordinates, Pi.mulSingle_apply, shortHeightIndex, Subtype.ext_iff]

private theorem short_coordinates_other (K : Type) [Field K] (σ : K ≃+* K)
    {h : ℤ} (s t : ShortAt h) (hst : s ≠ t) (a : Multiplicative K) (k : Fin 3) :
    shortSectionCoordinates K σ s.val s.property a (shortHeightIndex t.val k t.property) = 1 := by
  have hn (l : Fin 3) :
      shortHeightIndex s.val l s.property ≠ shortHeightIndex t.val k t.property :=
    fun he => hst (short_index_first s t l k he)
  simp [shortSectionCoordinates, Pi.mulSingle_apply, hn, fun l => Ne.symm (hn l)]

private theorem short_coordinates_long (K : Type) [Field K] (σ : K ≃+* K)
    {h : ℤ} (s : ShortAt h) (t : LongAt h) (a : Multiplicative K) :
    shortSectionCoordinates K σ s.val s.property a (longHeightIndex t.val t.property) = 1 := by
  simp [shortSectionCoordinates, Pi.mulSingle_apply, shortHeightIndex, longHeightIndex,
    Subtype.ext_iff]

def longCoordinateProduct (K : Type) [Field K] (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) : WordHeightIndex h → Multiplicative K :=
  ∏ s : LongAt h, Pi.mulSingle (longHeightIndex s.val s.property)
    (c (longHeightIndex s.val s.property))

def shortCoordinateProduct (K : Type) [Field K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) : WordHeightIndex h → Multiplicative K :=
  ∏ s : ShortAt h, shortSectionCoordinates K σ s.val s.property
    (c (shortHeightIndex s.val 0 s.property))

theorem fixed_coordinate_decomposition (K : Type) [Field K] (σ : K ≃+* K)
    (h : ℤ) (c : WordHeightIndex h → Multiplicative K)
    (hc : coordinateTwist K σ h c = c) :
    longCoordinateProduct K h c * shortCoordinateProduct K σ h c = c := by
  funext j
  rcases j with ⟨s | ⟨s,k⟩, hj⟩
  · have hs : ![(1 : ℤ),4,5] s = h := (long_height s).symm.trans hj
    let a : LongAt h := ⟨s,hs⟩
    change (longCoordinateProduct K h c) (longHeightIndex a.val a.property) *
      (shortCoordinateProduct K σ h c) (longHeightIndex a.val a.property) = _
    have hlong : (longCoordinateProduct K h c) (longHeightIndex a.val a.property) =
        c (longHeightIndex a.val a.property) := by
      unfold longCoordinateProduct
      rw [Finset.prod_apply, Finset.prod_eq_single a]
      · simp [Pi.mulSingle_apply]
      · intro b hb hba
        have hn : longHeightIndex b.val b.property ≠ longHeightIndex a.val a.property :=
          fun he => hba (long_index_injective h he)
        simp [Pi.mulSingle_apply, hn, Ne.symm hn]
      · simp
    have hshort : (shortCoordinateProduct K σ h c) (longHeightIndex a.val a.property) = 1 := by
      simp only [shortCoordinateProduct, Finset.prod_apply, short_coordinates_long,
        Finset.prod_const_one]
    rw [hlong,hshort,mul_one]
    exact congrArg c (Subtype.ext rfl)
  · have hs : ![(1 : ℤ),2,3] s = h := (short_label_height s k).symm.trans hj
    let a : ShortAt h := ⟨s,hs⟩
    change (longCoordinateProduct K h c) (shortHeightIndex a.val k a.property) *
      (shortCoordinateProduct K σ h c) (shortHeightIndex a.val k a.property) = _
    have hlong : (longCoordinateProduct K h c) (shortHeightIndex a.val k a.property) = 1 := by
      simp [longCoordinateProduct, Finset.prod_apply, Pi.mulSingle_apply,
        longHeightIndex, shortHeightIndex, Subtype.ext_iff]
    have hshort : (shortCoordinateProduct K σ h c) (shortHeightIndex a.val k a.property) =
        c (shortHeightIndex a.val k a.property) := by
      unfold shortCoordinateProduct
      rw [Finset.prod_apply, Finset.prod_eq_single a]
      · rw [short_coordinates_at]
        apply (Multiplicative.toAdd : Multiplicative K ≃ K).injective
        have he := fixed_short_parameters K σ h c hc a.val a.property k
        fin_cases k <;> exact he.symm
      · intro b hb hba
        exact short_coordinates_other K σ b a hba _ k
      · simp
    rw [hlong,hshort,one_mul]
    exact congrArg c (Subtype.ext rfl)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateDecomposition
