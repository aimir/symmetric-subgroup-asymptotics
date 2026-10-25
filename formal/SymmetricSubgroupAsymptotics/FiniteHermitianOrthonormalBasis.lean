import SymmetricSubgroupAsymptotics.FiniteHermitianUnitPerpDimension
import SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalBasisStep

/-! Gram--Schmidt for an actual finite-dimensional Hermitian subspace.
At each step norm surjectivity normalizes a nonisotropic vector; the
literal perpendicular inside that SAME subspace is nondegenerate and
has dimension one less. No named-group or order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalBasis
open Module CFSGTwistedAUnitaryParameters
open FiniteHermitianUnitPerp

theorem exists_subspace_basis {K I : Type*} [Field K] [Fintype I]
    (sigma : K ≃+* K) (H : Matrix I I K)
    (hnonfixed : ∃ a : K, sigma a ≠ a)
    (hswap : ∀ x y, hermitianPair sigma H x y=0 ↔ hermitianPair sigma H y x=0)
    (hfixed : ∀ x, sigma (hermitianPair sigma H x x)=hermitianPair sigma H x x)
    (hnorm : ∀ a : K, a ≠ 0 → sigma a=a → ∃ t : K, sigma t*t=a)
    (W : Submodule K (I → K))
    (hND : ∀ x ∈ W, (∀ y ∈ W, hermitianPair sigma H x y=0) → x=0) :
    ∃ b : Basis (Fin (Module.finrank K W)) K W,
      ∀ i j, hermitianPair sigma H (b i).val (b j).val=if i=j then 1 else 0 := by
  classical
  have hmain (n : ℕ) : ∀ U : Submodule K (I → K), Module.finrank K U=n →
      (∀ x ∈ U, (∀ y ∈ U, hermitianPair sigma H x y=0) → x=0) →
      ∃ b : Basis (Fin n) K U,
        ∀ i j, hermitianPair sigma H (b i).val (b j).val=if i=j then 1 else 0 := by
    induction n with
    | zero =>
      intro U hd _
      refine ⟨basisOfFinrankZero hd,?_⟩
      intro i
      exact Fin.elim0 i
    | succ n ih =>
      intro U hd hU
      haveI : Nontrivial U := (Module.finrank_pos_iff (R := K) (M := U)).mp (by omega)
      obtain ⟨v,hv,hone⟩ := FiniteHermitianUnitVectorSection.exists_unit_norm
        sigma H U hnonfixed hU hfixed hnorm
      let P := unitPerp sigma H U v
      have hdP : Module.finrank K P=n := by
        have hh := FiniteHermitianUnitPerpDimension.finrank_add_one sigma H U v hv hone
        change Module.finrank K P+1=Module.finrank K U at hh
        omega
      have hP : ∀ x ∈ P, (∀ y ∈ P, hermitianPair sigma H x y=0) → x=0 :=
        nondegenerate_unitPerp sigma H U v hv hone hswap hU
      obtain ⟨b,hb⟩ := ih P hdP hP
      exact FiniteHermitianOrthonormalBasisStep.exists_basis_step
        sigma H U v hv hone hswap b hb
  exact hmain (Module.finrank K W) W rfl hND

end SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalBasis
