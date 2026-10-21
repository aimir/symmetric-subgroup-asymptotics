import SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotentGroup

/-! The actual Suzuki unipotent subgroup fixes exactly its last coordinate
line. Consequently its matrix normalizer has zero last-column entries in
the first three rows. This is the normalizer exclusion needed for the
nontriangular Bruhat cell; no Bruhat or whole-group order premise is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
open Matrix CFSGSuzukiFieldParameters CFSG.Models.SuzukiConstruction

theorem twistedArray_fixed_iff {K : Type*} [CommRing K] [CharP K 2]
    (t : K →+* K) (v : Fin 4 → K) :
    (∀ a b, (twistedArray t a b).mulVec v = v) ↔
      v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro hv
    have h0 := congrArg (fun w : Fin 4 → K => w 2) (hv 0 1)
    have h0' : v 0 + v 2 = v 2 := by
      simpa [twistedArray, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h0
    have hv0 : v 0 = 0 := add_eq_right.mp h0'
    have h1 := congrArg (fun w : Fin 4 → K => w 3) (hv 0 1)
    simp [twistedArray, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hv0] at h1
    have hv1 : v 1 = 0 := h1
    have h2 := congrArg (fun w : Fin 4 → K => w 3) (hv 1 0)
    simp [twistedArray, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hv0, hv1] at h2
    exact ⟨hv0, hv1, h2⟩
  · rintro ⟨h0,h1,h2⟩ a b
    ext i
    fin_cases i <;>
      simp [twistedArray, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, h0, h1, h2]

def lastBasisVector (K : Type*) [Zero K] [One K] : Fin 4 → K :=
  ![0,0,0,1]

theorem last_column_zero_of_root_transport {K : Type*} [CommRing K] [CharP K 2]
    (t : K →+* K) (A : Matrix (Fin 4) (Fin 4) K)
    (hA : ∀ a b, ∃ c d,
      twistedArray t a b * A = A * twistedArray t c d) :
    A 0 3 = 0 ∧ A 1 3 = 0 ∧ A 2 3 = 0 := by
  let e := lastBasisVector K
  have he : ∀ a b, (twistedArray t a b).mulVec e = e :=
    (twistedArray_fixed_iff t e).mpr (by simp [e,lastBasisVector])
  have hf : ∀ a b, (twistedArray t a b).mulVec (A.mulVec e) = A.mulVec e := by
    intro a b
    obtain ⟨c,d,hcd⟩ := hA a b
    calc
      _ = (twistedArray t a b * A).mulVec e := Matrix.mulVec_mulVec _ _ _
      _ = (A * twistedArray t c d).mulVec e := congrArg (fun M => M.mulVec e) hcd
      _ = A.mulVec ((twistedArray t c d).mulVec e) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = _ := by rw [he]
  have hh := (twistedArray_fixed_iff t (A.mulVec e)).mp hf
  simpa [e,lastBasisVector,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh

theorem normalizer_last_column (m : ℕ) (A : Ambient m)
    (hA : A ∈ Subgroup.normalizer (unipotentSubgroup m : Set (Ambient m))) :
    (A : Mat m) 0 3 = 0 ∧ (A : Mat m) 1 3 = 0 ∧ (A : Mat m) 2 3 = 0 := by
  apply last_column_zero_of_root_transport (theta m) (A : Mat m)
  intro a b
  have ha : unipotentElement m a b ∈ unipotentSubgroup m := ⟨a,b,rfl⟩
  have hi : A⁻¹ ∈ Subgroup.normalizer (unipotentSubgroup m : Set (Ambient m)) :=
    (Subgroup.normalizer _).inv_mem hA
  have hc := (Subgroup.mem_normalizer_iff.mp hi (unipotentElement m a b)).mp ha
  obtain ⟨c,d,hcd⟩ := hc
  have hh : unipotentElement m a b * A = A * unipotentElement m c d := by
    calc
      _ = A * (A⁻¹ * unipotentElement m a b * (A⁻¹)⁻¹) := by group
      _ = _ := congrArg (fun z : Ambient m => A * z) hcd
  refine ⟨c,d,?_⟩
  have hm := congrArg (fun g : Ambient m => (g : Mat m)) hh
  simpa only [Units.val_mul,unipotentElement_coe,unipotent_eq_twistedArray] using hm

end SymmetricSubgroupAsymptotics.CFSGSuzukiUnipotent
