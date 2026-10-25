import SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusStabilizerIndex
import SymmetricSubgroupAsymptotics.ScalarInvariantSubspaceCardIndex

/-! Puncturing the SAME central annihilator improves the original Suzuki
quadratic/torus stabilizer index from (q-1)2^(m+1) to q*2^(m+1).
No change to the actual vector image or its anisotropy bound is made. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSuzukiPuncturedTorusStabilizerIndex
open CFSGSuzukiFieldParameters CFSGSuzukiCentralExtensionLayers
open CFSGSuzukiSubgroupPrimeFieldLayers CFSGSuzukiSquareIsotropy CFSGSuzukiCentralAnnihilatorIndex

theorem quadratic_torus_le_index (m : ℕ) (M : Subgroup (Borel m))
    (hM : ¬(centralHom m).range ≤ M.comap SemidirectProduct.inl) :
    Nat.card (Field m)*2^(m+1) ≤ M.index := by
  let q := Nat.card (Field m)
  let C := centralSubspace m (M.comap SemidirectProduct.inl)
  let c := Nat.card C
  let w := Nat.card (vectorSubspace m (M.comap SemidirectProduct.inl))
  let l := (M.map SemidirectProduct.rightHom).index
  have hc : c ≤ l := ScalarInvariantSubspaceCardIndex.card_le_index_of_surjective_scalars
    (centralWeight m) (centralWeight_surjective m) (M.map SemidirectProduct.rightHom) C
    (centralSubspace_stable m M) (centralSubspace_ne_top m _ hM)
  have he : M.index*c*w=q*q*l := index_mul_actual_layer_cards m M
  have hw : w ≤ 2^m := vectorSubspace_card_le m (M.comap SemidirectProduct.inl) hM
  have hmul : (q*q)*c ≤ (M.index*2^m)*c := by
    calc
      _ ≤ (q*q)*l := Nat.mul_le_mul_left _ hc
      _ = M.index*c*w := he.symm
      _ ≤ M.index*c*2^m := Nat.mul_le_mul_left _ hw
      _ = _ := by ring
  have hlo : q*q ≤ M.index*2^m :=
    Nat.le_of_mul_le_mul_right hmul (Nat.card_pos (α := C))
  have hp : 2^(m+1)*2^m=q := by
    rw [←pow_add]
    dsimp only [q]
    rw [field_card]
    congr 1
    omega
  have hh : (q*2^(m+1))*2^m ≤ M.index*2^m := by
    calc
      (q*2^(m+1))*2^m = q*q := by rw [mul_assoc,hp]
      _ ≤ _ := hlo
  exact Nat.le_of_mul_le_mul_right hh (pow_pos (by decide : 0 < (2 : ℕ)) m)

end SymmetricSubgroupAsymptotics.CFSGSuzukiPuncturedTorusStabilizerIndex
