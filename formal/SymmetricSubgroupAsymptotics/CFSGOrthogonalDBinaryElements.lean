import SymmetricSubgroupAsymptotics.CFSGOrthogonalDElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDRootBasisAction
import SymmetricSubgroupAsymptotics.CFSGSymplecticCoxeterPrefixAction

/-! Literal D root elements and the actual D Coxeter word. The common
chain prefix is reused as the same natural matrix word from type C;
its membership in the independently defined D subgroup is proved root
by root. The final fork factor is the original D fork root word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements
open CFSGOrthogonalDSerreMatrices

def rootElement (K : Type) [CommRing K] (r : ℕ) (neg : Bool) (i : Fin r) (a : K) :
    elementaryRootGroup K r := ⟨rootTransvection K r neg i a, rootTransvection_mem K r neg i a⟩

@[simp] theorem rootElement_zero (K : Type) [CommRing K] (r : ℕ)
    (neg : Bool) (i : Fin r) : rootElement K r neg i 0 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change 1 + (0 : K) • rootMatrix K r neg i = (1 : Mat K r)
  rw [zero_smul, add_zero]

theorem rootElement_add (K : Type) [CommRing K] (r : ℕ) (neg : Bool)
    (i : Fin r) (a b : K) :
    rootElement K r neg i (a + b) = rootElement K r neg i a * rootElement K r neg i b := by
  apply Subtype.ext
  apply Units.ext
  change 1 + (a + b) • rootMatrix K r neg i =
    (1 + a • rootMatrix K r neg i) * (1 + b • rootMatrix K r neg i)
  simp only [add_smul, mul_add, add_mul, mul_one, one_mul, smul_mul_assoc,
    mul_smul_comm, rootMatrix_sq_zero, smul_zero, add_zero]
  abel

theorem rootElement_inv (K : Type) [CommRing K] (r : ℕ) (neg : Bool)
    (i : Fin r) (a : K) : (rootElement K r neg i a)⁻¹ = rootElement K r neg i (-a) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← rootElement_add, add_neg_cancel, rootElement_zero]

def simpleWeyl (K : Type) [Field K] (r : ℕ) (i : Fin r) : elementaryRootGroup K r :=
  rootElement K r false i (-1) * rootElement K r true i 1 * rootElement K r false i (-1)

theorem chain_rootTransvection_eq_symplectic (K : Type) [Field K] (r : ℕ)
    (i : Fin r) (hi : i.val + 1 < r) (neg : Bool) (a : K) :
    rootTransvection K r neg i a =
      CFSGSymplecticSerreMatrices.rootTransvection K r neg i a := by
  apply Units.ext
  change 1 + a • rootMatrix K r neg i =
    1 + a • CFSGSymplecticSerreMatrices.rootMatrix K r neg i
  cases neg
  · simp only [rootMatrix, CFSGSymplecticSerreMatrices.rootMatrix, Bool.false_eq_true,
      if_false, chain_positive_eq_symplectic K r i hi]
  · simp only [rootMatrix, CFSGSymplecticSerreMatrices.rootMatrix, if_true,
      negative, CFSGSymplecticSerreMatrices.negative, chain_positive_eq_symplectic K r i hi]

theorem chain_simpleWeyl_eq_symplectic (K : Type) [Field K] (r : ℕ)
    (i : Fin r) (hi : i.val + 1 < r) :
    (simpleWeyl K r i).val = (CFSGSymplecticSerreMatrices.simpleWeyl K r i).val := by
  change rootTransvection K r false i (-1) * rootTransvection K r true i 1 *
      rootTransvection K r false i (-1) = _
  simp only [chain_rootTransvection_eq_symplectic K r i hi]
  rfl

theorem chainPrefix_mem (K : Type) [Field K] (r : ℕ) :
    (CFSGSymplecticSerreMatrices.chainWeylPrefix K r r).val ∈
      elementaryRootGroup K (r + 1) := by
  have aux : ∀ k : ℕ, k ≤ r →
      (CFSGSymplecticSerreMatrices.chainWeylPrefix K r k).val ∈
        elementaryRootGroup K (r + 1) := by
    intro k
    induction k with
    | zero => intro _; exact (elementaryRootGroup K (r + 1)).one_mem
    | succ k ih =>
      intro hk
      have hkr : k < r := by omega
      rw [CFSGSymplecticSerreMatrices.chainWeylPrefix_succ K r k hkr]
      apply (elementaryRootGroup K (r + 1)).mul_mem (ih (by omega))
      rw [← chain_simpleWeyl_eq_symplectic K (r + 1) (⟨k, hkr⟩ : Fin r).castSucc
        (by change k + 1 < r + 1; exact Nat.succ_lt_succ hkr)]
      exact (simpleWeyl K (r + 1) (⟨k, hkr⟩ : Fin r).castSucc).property
  exact aux r le_rfl

def chainPrefix (K : Type) [Field K] (r : ℕ) : elementaryRootGroup K (r + 1) :=
  ⟨(CFSGSymplecticSerreMatrices.chainWeylPrefix K r r).val, chainPrefix_mem K r⟩

def coxeterWeyl (K : Type) [Field K] (r : ℕ) : elementaryRootGroup K (r + 1) :=
  chainPrefix K r * simpleWeyl K (r + 1) (Fin.last r)

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements
