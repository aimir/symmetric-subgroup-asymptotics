import SymmetricSubgroupAsymptotics.CFSGSymplecticSimpleWeyl
import SymmetricSubgroupAsymptotics.CFSGMatrixPairRotationAction

/-! Literal basis action of the actual C simple Weyl words. These
local formulas supply the ordered Coxeter-cycle proof in all fields. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
open CFSGMatrixPairRotation

private theorem castSucc_ne_succ {r : ℕ} (i : Fin r) : i.castSucc ≠ i.succ := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = i.val + 1 at hv
  omega

theorem simpleWeyl_chain_positive_left (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) *ᵥ
        Pi.single (Sum.inl i.castSucc) 1 = Pi.single (Sum.inl i.succ) 1 := by
  rw [simpleWeyl_chain_val, ← Matrix.mulVec_mulVec]
  rw [rotation_basis_other K _ _ _ (by intro h; cases h) (by intro h; cases h)]
  exact rotation_basis_left K _ _ (fun h => castSucc_ne_succ i (Sum.inl.inj h))

theorem simpleWeyl_chain_positive_right (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) *ᵥ
        Pi.single (Sum.inl i.succ) 1 = -Pi.single (Sum.inl i.castSucc) 1 := by
  rw [simpleWeyl_chain_val, ← Matrix.mulVec_mulVec]
  rw [rotation_basis_other K _ _ _ (by intro h; cases h) (by intro h; cases h)]
  exact rotation_basis_right K _ _ (fun h => castSucc_ne_succ i (Sum.inl.inj h))

theorem simpleWeyl_chain_negative_left (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) *ᵥ
        Pi.single (Sum.inr i.castSucc) 1 = Pi.single (Sum.inr i.succ) 1 := by
  rw [simpleWeyl_chain_val, ← Matrix.mulVec_mulVec,
    rotation_basis_left K _ _ (fun h => castSucc_ne_succ i (Sum.inr.inj h))]
  exact rotation_basis_other K _ _ _ (by intro h; cases h) (by intro h; cases h)

theorem simpleWeyl_chain_negative_right (K : Type) [Field K] (r : ℕ) (i : Fin r) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) *ᵥ
        Pi.single (Sum.inr i.succ) 1 = -Pi.single (Sum.inr i.castSucc) 1 := by
  rw [simpleWeyl_chain_val, ← Matrix.mulVec_mulVec,
    rotation_basis_right K _ _ (fun h => castSucc_ne_succ i (Sum.inr.inj h)), Matrix.mulVec_neg]
  exact congrArg Neg.neg (rotation_basis_other K _ _ _ (by intro h; cases h) (by intro h; cases h))

theorem simpleWeyl_chain_other (K : Type) [Field K] (r : ℕ) (i : Fin r) (x : Index (r + 1))
    (hp : x ≠ Sum.inl i.castSucc) (hp' : x ≠ Sum.inl i.succ)
    (hn : x ≠ Sum.inr i.castSucc) (hn' : x ≠ Sum.inr i.succ) :
    ((simpleWeyl K (r + 1) i.castSucc).val : Mat K (r + 1)) *ᵥ Pi.single x 1 = Pi.single x 1 := by
  rw [simpleWeyl_chain_val, ← Matrix.mulVec_mulVec,
    rotation_basis_other K _ _ x hn hn']
  exact rotation_basis_other K _ _ x hp hp'

theorem simpleWeyl_terminal_positive (K : Type) [Field K] (r : ℕ) :
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ
      Pi.single (Sum.inl (Fin.last r)) 1 = Pi.single (Sum.inr (Fin.last r)) 1 := by
  rw [simpleWeyl_terminal_val]
  exact rotation_basis_left K _ _ (by intro h; cases h)

theorem simpleWeyl_terminal_negative (K : Type) [Field K] (r : ℕ) :
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ
      Pi.single (Sum.inr (Fin.last r)) 1 = -Pi.single (Sum.inl (Fin.last r)) 1 := by
  rw [simpleWeyl_terminal_val]
  exact rotation_basis_right K _ _ (by intro h; cases h)

theorem simpleWeyl_terminal_other (K : Type) [Field K] (r : ℕ) (x : Index (r + 1))
    (hp : x ≠ Sum.inl (Fin.last r)) (hn : x ≠ Sum.inr (Fin.last r)) :
    ((simpleWeyl K (r + 1) (Fin.last r)).val : Mat K (r + 1)) *ᵥ Pi.single x 1 = Pi.single x 1 := by
  rw [simpleWeyl_terminal_val]
  exact rotation_basis_other K _ _ x hp hn

end SymmetricSubgroupAsymptotics.CFSGSymplecticSerreMatrices
