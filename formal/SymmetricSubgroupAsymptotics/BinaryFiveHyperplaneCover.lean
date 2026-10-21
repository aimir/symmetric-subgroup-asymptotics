import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import SymmetricSubgroupAsymptotics.BinaryLinearConstraintCertificate
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi

/-! Every proper subspace of a literal5-dimensional binary chart lies
in one of its31 nonzero coordinate hyperplanes. This is linear dual
separation of the actual subspace, not a normal-subgroup catalogue. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics
local instance fiveHyperplaneCoverFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem five_mask_surjective : ∀ v : Fin 5 → ZMod 2,
    ∃ c : Fin 32, binaryVectorOfMask 5 c.val=v := by decide +kernel

/-- These hyperplanes retain their original ambient chart inclusion. -/
def binaryFiveHyperplane {w : ℕ} (C : BinaryCoordinateSpace w 5) (c : Fin 32) :
    Submodule (ZMod 2) (Fin w → ZMod 2) :=
  C.space ⊓ ((binaryRowFunctional (binaryVectorOfMask 5 c.val)).comp C.coordinates).ker

/-- No invariance premise is needed for the linear covering step. -/
theorem exists_nonzero_binaryFiveHyperplane_of_proper
    {w : ℕ} (C : BinaryCoordinateSpace w 5)
    (A : Submodule (ZMod 2) (Fin w → ZMod 2)) (hAC : A≤C.space) (hproper : A≠C.space) :
    ∃ c : Fin 32, c≠0 ∧ A≤binaryFiveHyperplane C c := by
  let P : Submodule (ZMod 2) (Fin 5 → ZMod 2) := A.comap C.inclusion
  have hP : P≠⊤ := by
    intro he
    apply hproper
    apply le_antisymm hAC
    rintro v ⟨a,rfl⟩
    have ha : a∈P := by rw [he];exact Submodule.mem_top
    exact ha
  obtain ⟨f,hf,hkill⟩ := P.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hP)
    inferInstance
  let coeff : Fin 5 → ZMod 2 := fun i => f (Pi.single i 1)
  have heq : binaryRowFunctional coeff=f :=
    binaryLinearFunctional_ext_basis (fun i => by
      change dotProduct coeff (Pi.single i 1)=f (Pi.single i 1)
      rw [dotProduct_single_one])
  obtain ⟨c,hc⟩ := five_mask_surjective coeff
  have hc0 : c≠0 := by
    intro hz
    apply hf
    have hzcoeff : coeff=0 := by
      rw [hz] at hc
      have hzero : binaryVectorOfMask 5 0=(0 : Fin 5 → ZMod 2) := by decide +kernel
      exact hc.symm.trans hzero
    rw [←heq,hzcoeff]
    apply LinearMap.ext
    intro v
    simp [binaryRowFunctional,dotProduct]
  refine ⟨c,hc0,?_⟩
  intro v hv
  refine ⟨hAC hv,?_⟩
  change binaryRowFunctional (binaryVectorOfMask 5 c.val) (C.coordinates v)=0
  rw [hc,heq]
  have ha : C.coordinates v∈P := by
    change C.inclusion (C.coordinates v)∈A
    rw [(C.mem_iff v).mp (hAC hv)]
    exact hv
  have hm : f (C.coordinates v)∈P.map f := ⟨C.coordinates v,ha,rfl⟩
  rw [hkill] at hm
  exact (Submodule.mem_bot (R := ZMod 2)).mp hm

end SymmetricSubgroupAsymptotics
