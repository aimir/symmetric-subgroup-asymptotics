import SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotentCenterConverse
import Mathlib.Algebra.CharP.Two
import Mathlib.SetTheory.Cardinal.Finite

/-! The actual characteristic-two unipotent centre has its literal
two additive field coordinates. The isomorphism is proved from the
same matrix entries; no dimension or root-family premise is supplied. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K] [CharP K 2]

def centerParameterElement (r : ℕ) (hr : 0 < r) (a b : K) : unipotent K (r + 1) :=
  highestLongInU r hr a * highestShortInU r hr b

theorem centerParameterElement_matrix (r : ℕ) (hr : 0 < r) (a b : K) :
    let k : Fin (r + 1) := ⟨1, by omega⟩
    ((centerParameterElement (K := K) r hr a b).val.val : Mat K (r + 1)) =
      Matrix.fromBlocks 1 (Matrix.single 0 0 a + Matrix.single 0 k b + Matrix.single k 0 b) 0 1 := by
  let k : Fin (r + 1) := ⟨1, by omega⟩
  have hL : ((highestLongInU r hr a).val.val : Mat K (r + 1)) =
      Matrix.fromBlocks 1 (Matrix.diagonal (Pi.single 0 a)) 0 1 := rfl
  have hS : ((highestShortInU r hr b).val.val : Mat K (r + 1)) =
      Matrix.fromBlocks 1 (Matrix.single 0 k b + Matrix.single k 0 b) 0 1 := rfl
  change ((highestLongInU r hr a).val.val : Mat K (r + 1)) *
    ((highestShortInU r hr b).val.val : Mat K (r + 1)) = _
  rw [hL, hS, Matrix.fromBlocks_multiply, Matrix.diagonal_single]
  simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  apply congrArg (fun B : Matrix (Fin (r + 1)) (Fin (r + 1)) K =>
    (Matrix.fromBlocks 1 B 0 1 : Mat K (r + 1)))
  abel

def centerParameterHom (r : ℕ) (hr : 0 < r) :
    Multiplicative (K × K) →* Subgroup.center (unipotent K (r + 1)) where
  toFun x := ⟨centerParameterElement r hr x.toAdd.1 x.toAdd.2,
    (center_two_parameter_iff r hr _).mpr
      ⟨x.toAdd.1, x.toAdd.2, by rw [CharTwo.two_eq_zero, zero_mul], rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change ((centerParameterElement r hr (0 : K) 0).val.val : Mat K (r + 1)) = 1
    rw [centerParameterElement_matrix]
    simp only [Matrix.single_zero, add_zero, Matrix.fromBlocks_one]
  map_mul' x y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change ((centerParameterElement r hr (x.toAdd.1 + y.toAdd.1)
        (x.toAdd.2 + y.toAdd.2)).val.val : Mat K (r + 1)) =
      ((centerParameterElement r hr x.toAdd.1 x.toAdd.2).val.val : Mat K (r + 1)) *
        ((centerParameterElement r hr y.toAdd.1 y.toAdd.2).val.val : Mat K (r + 1))
    rw [centerParameterElement_matrix, centerParameterElement_matrix,
      centerParameterElement_matrix, Matrix.fromBlocks_multiply]
    simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, Matrix.single_add]
    congr 1
    abel

theorem centerParameterHom_injective (r : ℕ) (hr : 0 < r) :
    Function.Injective (centerParameterHom (K := K) r hr) := by
  intro x y he
  let k : Fin (r + 1) := ⟨1, by omega⟩
  have h00 := congrArg (fun z : Subgroup.center (unipotent K (r + 1)) =>
    (z.val.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inr 0)) he
  have h01 := congrArg (fun z : Subgroup.center (unipotent K (r + 1)) =>
    (z.val.val.val : Mat K (r + 1)) (Sum.inl 0) (Sum.inr k)) he
  change ((centerParameterElement r hr x.toAdd.1 x.toAdd.2).val.val : Mat K (r + 1))
      (Sum.inl 0) (Sum.inr 0) =
    ((centerParameterElement r hr y.toAdd.1 y.toAdd.2).val.val : Mat K (r + 1))
      (Sum.inl 0) (Sum.inr 0) at h00
  change ((centerParameterElement r hr x.toAdd.1 x.toAdd.2).val.val : Mat K (r + 1))
      (Sum.inl 0) (Sum.inr k) =
    ((centerParameterElement r hr y.toAdd.1 y.toAdd.2).val.val : Mat K (r + 1))
      (Sum.inl 0) (Sum.inr k) at h01
  rw [centerParameterElement_matrix, centerParameterElement_matrix] at h00 h01
  have ha : x.toAdd.1 = y.toAdd.1 := by
    simpa [Matrix.fromBlocks, Matrix.single_apply, k] using h00
  have hb : x.toAdd.2 = y.toAdd.2 := by
    simpa [Matrix.fromBlocks, Matrix.single_apply, k] using h01
  exact Multiplicative.toAdd.injective (Prod.ext ha hb)

theorem centerParameterHom_surjective (r : ℕ) (hr : 0 < r) :
    Function.Surjective (centerParameterHom (K := K) r hr) := by
  intro z
  obtain ⟨a, b, _, hab⟩ := (center_two_parameter_iff r hr z.val).mp z.property
  refine ⟨Multiplicative.ofAdd (a, b), ?_⟩
  exact Subtype.ext hab.symm

def binaryCenterEquiv (r : ℕ) (hr : 0 < r) :
    Multiplicative (K × K) ≃* Subgroup.center (unipotent K (r + 1)) :=
  MulEquiv.ofBijective (centerParameterHom r hr)
    ⟨centerParameterHom_injective r hr, centerParameterHom_surjective r hr⟩

theorem binary_unipotent_center_card (r : ℕ) (hr : 0 < r) :
    Nat.card (Subgroup.center (unipotent K (r + 1))) = Nat.card K ^ 2 := by
  calc
    _ = Nat.card (Multiplicative (K × K)) := Nat.card_congr (binaryCenterEquiv r hr).symm.toEquiv
    _ = Nat.card (K × K) := Nat.card_congr Multiplicative.toAdd
    _ = Nat.card K ^ 2 := by rw [Nat.card_prod, pow_two]

end SymmetricSubgroupAsymptotics.CFSGSymplecticUnipotent
