import SymmetricSubgroupAsymptotics.PermutationInvariantCoordinateSeparation
import SymmetricSubgroupAsymptotics.SignedMonomialFixedCoordinateCode
import SymmetricSubgroupAsymptotics.DistinctDiagonalFullSubmodule

/-! A nonzero proper transitive monomial submodule forces every actual
permutation-invariant diagonal scalar codeword to be constant. Signed
monomial lifts remain signed throughout; no classification of unsigned
S4 submodules or of sign codes is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ProperTransitiveMonomialScalarCode

theorem coordinate_nonzero_of_transitive_monomial
    {G I K : Type*} [Group G] [Field K]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))
    (htrans : ∀ i j,∃g : G,t g i=j)
    (W : Submodule K (I → K)) (hne : W≠⊥)
    (hstable : ∀g w,w∈W → ρ g w∈W) :
    ∀ i,∃w : W,w.val i≠0 := by
  obtain ⟨w,hw,hwn⟩ := W.ne_bot_iff.mp hne
  have hj : ∃j,w j≠0 := by
    by_contra h
    apply hwn
    funext j
    exact Classical.byContradiction (fun hj => h ⟨j,hj⟩)
  obtain ⟨j,hj⟩ := hj
  intro i
  obtain ⟨g,hg⟩ := htrans j i
  refine ⟨⟨ρ g w,hstable g w hw⟩,?_⟩
  have hgi : (t g).symm i=j := by
    rw [←hg]
    exact (t g).symm_apply_apply j
  change ρ g w i≠0
  rw [hformula,hgi]
  exact mul_ne_zero (a g i).ne_zero hj

theorem eq_top_of_nonconstant_diagonal_code
    {I K : Type*} [Field K] [Fintype I]
    (C : Set (I → K))
    (hperm : ∀ (s : Equiv.Perm I) (c : I → K),c∈C → c ∘ s∈C)
    (hnot : ¬∀ (c : I → K),c∈C → ∀ i j,c i=c j)
    (W : Submodule K (I → K))
    (hstable : ∀ (c : I → K),c∈C → ∀w,w∈W → (fun i => c i*w i)∈W)
    (hnonzero : ∀i,∃w : W,w.val i≠0) : W=⊤ := by
  let scalar : I → {c : I → K // c∈C} → K := fun i c => c.val i
  have hinj : Function.Injective scalar :=
    PermutationInvariantCoordinateSeparation.coordinate_evaluations_injective_of_not_constant
      C hperm hnot
  let S : DiagonalInvariantSubmodules.Stable scalar := ⟨W,by
    intro c w hw
    exact hstable c.val c.property w hw⟩
  apply DiagonalInvariantSubmodules.eq_top_of_fullCoordinates_of_injective scalar hinj S
  intro i c
  obtain ⟨w,hw⟩ := hnonzero i
  refine ⟨(c*(w.val i)⁻¹) • w,?_⟩
  change (c*(w.val i)⁻¹)*w.val i=c
  rw [mul_assoc,inv_mul_cancel₀ hw,mul_one]

theorem scalar_code_constant_of_proper_transitive_monomial_submodule
    {G I K : Type*} [Group G] [Field K] [Fintype I]
    (ρ : G →* ((I → K) ≃ₗ[K] (I → K)))
    (t : G →* Equiv.Perm I) (a : G → I → Kˣ)
    (hformula : ∀ (g : G) (w : I → K) (i : I),
      ρ g w i=(a g i : K)*w ((t g).symm i))
    (htrans : ∀ i j,∃g : G,t g i=j)
    (W : Submodule K (I → K)) (hne : W≠⊥) (hproper : W≠⊤)
    (hstable : ∀g w,w∈W → ρ g w∈W)
    (C : Set (I → K))
    (hperm : ∀ (s : Equiv.Perm I) (c : I → K),c∈C → c ∘ s∈C)
    (hdiag : ∀ (c : I → K),c∈C → ∀w,w∈W → (fun i => c i*w i)∈W) :
    ∀ (c : I → K),c∈C → ∀ i j,c i=c j := by
  by_contra hnot
  apply hproper
  exact eq_top_of_nonconstant_diagonal_code C hperm hnot W hdiag
    (coordinate_nonzero_of_transitive_monomial ρ t a hformula htrans W hne hstable)

end SymmetricSubgroupAsymptotics.ProperTransitiveMonomialScalarCode
