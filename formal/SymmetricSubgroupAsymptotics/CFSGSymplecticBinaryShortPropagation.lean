import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryLongPropagation

/-! The recovered short-root array propagates along every actual chain.
Two original Coxeter steps across the terminal pair give the negative
chain, without requiring an abstract Weyl orbit theorem. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryShortPropagation
open Matrix CFSGSymplecticSerreMatrices CFSGSymplecticBinaryRotationArrays
open CFSGSymplecticBinaryCoxeterMatrix CFSGSymplecticBinaryPairElements
open CFSGSymplecticBinaryArrayMembership CFSGSymplecticBinaryPairExtraction
variable {K : Type} [Field K] [CharP K 2]

theorem side_short_mem (s : ℕ) (H : Subgroup ((Mat K (s+3))ˣ))
    (hW : (binarySecond K s).val∈H) (side : Bool)
    (h0 : HasArray H (shortArray
      (if side then Sum.inr (0 : Fin (s+3)) else Sum.inl 0)
      (if side then Sum.inr (⟨1,by omega⟩ : Fin (s+3)) else Sum.inl ⟨1,by omega⟩))) :
    ∀k : ℕ,∀hk : k<s+2,HasArray H (shortArray
      (if side then Sum.inr (⟨k,by omega⟩ : Fin (s+3)) else Sum.inl ⟨k,by omega⟩)
      (if side then Sum.inr (⟨k+1,by omega⟩ : Fin (s+3)) else Sum.inl ⟨k+1,by omega⟩)) := by
  intro k
  induction k with
  | zero => intro hk;exact h0
  | succ k ih =>
    intro hk
    have hh := hasArray_conjugate_short (s+2) H hW _ _ (ih (by omega))
    rw [cyclePerm_shift (s+2) side k (by omega),
      cyclePerm_shift (s+2) side (k+1) (by omega)] at hh
    exact hh

theorem all_chain_short_mem (s : ℕ) (H : Subgroup ((Mat K (s+3))ˣ))
    (hX : (binaryFirst K s).val∈H) (hW : (binarySecond K s).val∈H) :
    ∀side : Bool,∀k : ℕ,∀hk : k<s+2,HasArray H (shortArray
      (if side then Sum.inr (⟨k,by omega⟩ : Fin (s+3)) else Sum.inl ⟨k,by omega⟩)
      (if side then Sum.inr (⟨k+1,by omega⟩ : Fin (s+3)) else Sum.inl ⟨k+1,by omega⟩)) := by
  have h01 := short_zero_one_mem s H hX hW
  have hpos := side_short_mem s H hW false h01
  have hlast := hpos (s+1) (by omega)
  have hcross := hasArray_conjugate_short (s+2) H hW _ _ hlast
  have hleft : cyclePerm (s+2) (Sum.inl (⟨s+1,by omega⟩ : Fin (s+3)))=
      Sum.inl (Fin.last (s+2)) := by
    simpa only [Bool.false_eq_true,if_false] using cyclePerm_shift (s+2) false (s+1) (by omega)
  have hright : cyclePerm (s+2) (Sum.inl (⟨s+2,by omega⟩ : Fin (s+3)))=
      Sum.inr (0 : Fin (s+3)) := cyclePerm_positive_last (s+2)
  simp only [Bool.false_eq_true,if_false] at hcross
  rw [hleft,hright] at hcross
  have hneg0 := hasArray_conjugate_short (s+2) H hW _ _ hcross
  rw [cyclePerm_positive_last] at hneg0
  have hnext : cyclePerm (s+2) (Sum.inr (0 : Fin (s+3)))=
      Sum.inr (⟨1,by omega⟩ : Fin (s+3)) := by
    simpa only [eq_self_iff_true,if_true] using cyclePerm_shift (s+2) true 0 (by omega)
  rw [hnext] at hneg0
  have hneg := side_short_mem s H hW true hneg0
  intro side
  cases side
  · exact hpos
  · exact hneg

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryShortPropagation
