import SymmetricSubgroupAsymptotics.CFSGFiniteHermitianSimilitudeRigidity
import SymmetricSubgroupAsymptotics.CFSGHermitianOrthogonalSpan
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The actual finite Hermitian perpendicular is an involutive order
reversal. The proof represents separating dual functionals by the literal
invertible matrix pairing, rather than assuming a polar-space duality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGFiniteHermitianPerpLattice
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I : Type*} [Field K] [Finite K] [Fintype I] [DecidableEq I]
variable (sigma : K ≃+* K) (H : (Matrix I I K)ˣ)

omit [Finite K] in
theorem rightPerp_antitone : Antitone (rightPerp sigma (H : Matrix I I K)) := by
  intro S T hST y hy x hx
  exact hy x (hST hx)

omit [Finite K] in
theorem rightPerp_sup (S T : Submodule K (I → K)) :
    rightPerp sigma H (S ⊔ T) = rightPerp sigma H S ⊓ rightPerp sigma H T := by
  apply le_antisymm
  · intro y hy
    exact ⟨fun x hx => hy x ((show S ≤ S ⊔ T from le_sup_left) hx),
      fun x hx => hy x ((show T ≤ S ⊔ T from le_sup_right) hx)⟩
  · intro y hy x hx
    obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
    rw [hermitianPair_add_left, hy.1 s hs, hy.2 t ht, zero_add]

theorem rightPerp_rightPerp
    (hswap : ∀ x y, hermitianPair sigma (H : Matrix I I K) x y = 0 ↔ hermitianPair sigma (H : Matrix I I K) y x = 0)
    (S : Submodule K (I → K)) : rightPerp sigma H (rightPerp sigma H S) = S := by
  apply le_antisymm
  · intro x hx
    apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S x).mp
    intro f hf
    obtain ⟨y, hy⟩ := CFSGFiniteHermitianSimilitudeRigidity.hermitianDual_surjective sigma H f
    have hyS : y ∈ rightPerp sigma H S := by
      intro z hz
      have hh := (S.mem_dualAnnihilator f).mp hf z hz
      have he := congrArg (fun L : Module.Dual K (I → K) => L z) hy
      have hyz : hermitianPair sigma (H : Matrix I I K) y z = 0 := he.trans hh
      exact (hswap y z).mp hyz
    have hyx : hermitianPair sigma (H : Matrix I I K) y x = 0 := hx y hyS
    exact (congrArg (fun L : Module.Dual K (I → K) => L x) hy).symm.trans hyx
  · intro x hx y hy
    exact (hswap x y).mp (hy x hx)

theorem perp_intersection_le_implies_perp_le_sup
    (hswap : ∀ x y, hermitianPair sigma (H : Matrix I I K) x y = 0 ↔ hermitianPair sigma (H : Matrix I I K) y x = 0)
    (S T W : Submodule K (I → K))
    (h : rightPerp sigma H S ⊓ rightPerp sigma H T ≤ W) :
    rightPerp sigma H W ≤ S ⊔ T := by
  have hh := rightPerp_antitone sigma H h
  rw [← rightPerp_sup, rightPerp_rightPerp sigma H hswap] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGFiniteHermitianPerpLattice
