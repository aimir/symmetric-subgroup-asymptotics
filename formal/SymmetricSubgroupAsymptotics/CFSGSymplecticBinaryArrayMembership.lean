import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPairElements

/-! Sparse-array membership certificates for actual matrix-unit subgroups.
Every witness is an original unit in the same subgroup. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryArrayMembership
open Matrix CFSGSymplecticSerreMatrices CFSGSymplecticBinaryRotationArrays
open CFSGSymplecticBinaryCoxeterMatrix CFSGSymplecticBinaryConjugation
variable {K : Type} [Field K] [CharP K 2] {r : ℕ}

def HasArray (H : Subgroup ((Mat K r)ˣ)) (A : Mat K r) : Prop :=
  ∃g : (Mat K r)ˣ,g∈H ∧ (g : Mat K r)=A

theorem hasArray_one (H : Subgroup ((Mat K r)ˣ)) : HasArray H 1 := ⟨1,H.one_mem,rfl⟩

theorem hasArray_mul {H : Subgroup ((Mat K r)ˣ)} {A B : Mat K r}
    (hA : HasArray H A) (hB : HasArray H B) : HasArray H (A*B) := by
  obtain ⟨a,ha,hea⟩ := hA
  obtain ⟨b,hb,heb⟩ := hB
  exact ⟨a*b,H.mul_mem ha hb,by change (a : Mat K r)*(b : Mat K r)=A*B;rw [hea,heb]⟩

theorem hasArray_pow {H : Subgroup ((Mat K r)ˣ)} {A : Mat K r}
    (hA : HasArray H A) (k : ℕ) : HasArray H (A^k) := by
  obtain ⟨a,ha,hea⟩ := hA
  refine ⟨a^k,H.pow_mem ha k,?_⟩
  simpa only [Units.val_pow_eq_pow_val,hea]

theorem hasArray_iff_mem (H : Subgroup ((Mat K r)ˣ)) (g : (Mat K r)ˣ) :
    HasArray H (g : Mat K r)↔g∈H := by
  constructor
  · rintro ⟨a,ha,he⟩
    exact (Units.ext he) ▸ ha
  · intro h
    exact ⟨g,h,rfl⟩

theorem hasArray_conjugate_long (s : ℕ) (H : Subgroup ((Mat K (s+1))ˣ))
    (hW : (coxeterWeyl K s).val∈H) (a : Index (s+1)) (ha : HasArray H (longArray a)) :
    HasArray H (longArray (cyclePerm s a)) := by
  obtain ⟨g,hg,he⟩ := ha
  refine ⟨(coxeterWeyl K s).val*g*(coxeterWeyl K s).val⁻¹,
    H.mul_mem (H.mul_mem hW hg) (H.inv_mem hW),?_⟩
  change ((coxeterWeyl K s).val : Mat K (s+1))*(g : Mat K (s+1))*
    (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))=_
  rw [he,conjugation_long]

theorem hasArray_conjugate_short (s : ℕ) (H : Subgroup ((Mat K (s+1))ˣ))
    (hW : (coxeterWeyl K s).val∈H) (a b : Index (s+1)) (ha : HasArray H (shortArray a b)) :
    HasArray H (shortArray (cyclePerm s a) (cyclePerm s b)) := by
  obtain ⟨g,hg,he⟩ := ha
  refine ⟨(coxeterWeyl K s).val*g*(coxeterWeyl K s).val⁻¹,
    H.mul_mem (H.mul_mem hW hg) (H.inv_mem hW),?_⟩
  change ((coxeterWeyl K s).val : Mat K (s+1))*(g : Mat K (s+1))*
    (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))=_
  rw [he,conjugation_short]

theorem hasArray_inverse_conjugate_short (s : ℕ) (H : Subgroup ((Mat K (s+1))ˣ))
    (hW : (coxeterWeyl K s).val∈H) (a b : Index (s+1)) (ha : HasArray H (shortArray a b)) :
    HasArray H (shortArray ((cyclePerm s).symm a) ((cyclePerm s).symm b)) := by
  obtain ⟨g,hg,he⟩ := ha
  refine ⟨(coxeterWeyl K s).val⁻¹*g*(coxeterWeyl K s).val,
    H.mul_mem (H.mul_mem (H.inv_mem hW) hg) hW,?_⟩
  change (↑((coxeterWeyl K s).val⁻¹) : Mat K (s+1))*(g : Mat K (s+1))*
    ((coxeterWeyl K s).val : Mat K (s+1))=_
  rw [he,inverse_conjugation_short]

end SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryArrayMembership
