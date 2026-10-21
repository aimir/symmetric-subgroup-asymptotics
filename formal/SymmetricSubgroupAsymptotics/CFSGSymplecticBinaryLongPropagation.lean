import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPairExtraction

/-! Propagation of the recovered actual long-root array through every
original positive and negative coordinate of the Coxeter cycle. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryLongPropagation
open Matrix CFSGSymplecticSerreMatrices CFSGSymplecticBinaryRotationArrays
open CFSGSymplecticBinaryCoxeterMatrix CFSGSymplecticBinaryConjugation
open CFSGSymplecticBinaryPairElements CFSGSymplecticBinaryArrayMembership
open CFSGSymplecticBinaryPairExtraction
variable {K : Type} [Field K] [CharP K 2]

theorem preimage_long_mem (s : ℕ) (H : Subgroup ((Mat K (s+1))ˣ))
    (hW : (coxeterWeyl K s).val∈H) (a : Index (s+1))
    (ha : HasArray H (longArray (cyclePerm s a))) : HasArray H (longArray a) := by
  obtain ⟨g,hg,he⟩ := ha
  refine ⟨(coxeterWeyl K s).val⁻¹*g*(coxeterWeyl K s).val,
    H.mul_mem (H.mul_mem (H.inv_mem hW) hg) hW,?_⟩
  change (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))*(g : Mat K (s+1))*
    ((coxeterWeyl K s).val : Mat K (s+1))=_
  rw [he]
  have hh := conjugation_long (K:=K) s a
  have hc := congrArg (fun A : Mat K (s+1) =>
    (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))*A*((coxeterWeyl K s).val : Mat K (s+1))) hh
  simpa only [mul_assoc,Units.inv_mul_cancel_left,Units.inv_mul,Units.mul_inv,one_mul,mul_one] using hc.symm

theorem side_long_mem (s : ℕ) (H : Subgroup ((Mat K (s+1))ˣ))
    (hW : (coxeterWeyl K s).val∈H) (side : Bool)
    (h0 : HasArray H (longArray (if side then Sum.inr (0 : Fin (s+1)) else Sum.inl 0))) :
    ∀i : Fin (s+1),HasArray H (longArray (if side then Sum.inr i else Sum.inl i)) := by
  have aux : ∀k : ℕ,∀hk : k≤s,
      HasArray H (longArray (if side then Sum.inr (⟨k,by omega⟩ : Fin (s+1)) else Sum.inl ⟨k,by omega⟩)) := by
    intro k
    induction k with
    | zero => intro hk;exact h0
    | succ k ih =>
      intro hk
      have hh := hasArray_conjugate_long s H hW _ (ih (by omega))
      rw [cyclePerm_shift s side k (by omega)] at hh
      exact hh
  intro i
  exact aux i.val (by omega)

theorem all_long_mem (s : ℕ) (H : Subgroup ((Mat K (s+3))ˣ))
    (hX : (binaryFirst K s).val∈H) (hW : (binarySecond K s).val∈H) :
    ∀a : Index (s+3),HasArray H (longArray a) := by
  have h1 := long_negative_one_mem s H hX hW
  have hc : cyclePerm (s+2) (Sum.inr (0 : Fin (s+3)))=Sum.inr (⟨1,by omega⟩ : Fin (s+3)) := by
    simpa only [eq_self_iff_true,if_true] using cyclePerm_shift (s+2) true 0 (by omega)
  have h0 : HasArray H (longArray (Sum.inr (0 : Fin (s+3)))) := by
    apply preimage_long_mem (s+2) H hW
    rw [hc]
    exact h1
  have hneg := side_long_mem (s+2) H hW true h0
  have hlast := hneg (Fin.last (s+2))
  have hpos0 := hasArray_conjugate_long (s+2) H hW _ hlast
  simp only [eq_self_iff_true,if_true,cyclePerm_negative_last] at hpos0
  have hpos := side_long_mem (s+2) H hW false hpos0
  intro a
  cases a with
  | inl i => exact hpos i
  | inr i => exact hneg i

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryLongPropagation
