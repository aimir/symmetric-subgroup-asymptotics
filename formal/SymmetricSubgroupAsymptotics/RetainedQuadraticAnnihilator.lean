import SymmetricSubgroupAsymptotics.QuadraticSubspaceIncidence
import SymmetricSubgroupAsymptotics.AllLifts

/-!
# Original square annihilators in quadratic coordinates

The simultaneous coordinate equations are exactly the original square
annihilator transported by the dual coordinate isomorphism. The square-span
identification is proved from a pointwise equality of original squares.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {ι : Type*} [Fintype ι]

/-- The coefficients of an actual functional on the original binary kernel. -/
def binaryDualCoordinates : Module.Dual (ZMod 2) (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2) :=
  (Pi.basisFun (ZMod 2) ι).dualBasis.equivFun

theorem binaryDualCoordinates_eval (f : Module.Dual (ZMod 2) (ι → ZMod 2))
    (v : ι → ZMod 2) : f v = ∑ i, binaryDualCoordinates f i * v i := by
  rw [LinearMap.pi_apply_eq_sum_univ]
  apply Finset.sum_congr rfl
  intro i _
  simp only [binaryDualCoordinates, Module.Basis.dualBasis_equivFun, Pi.basisFun_apply,
    smul_eq_mul]
  rw [mul_comm (v i)]
  apply congrArg (fun z : ZMod 2 ↦ z * v i)
  apply congrArg f
  funext j
  simp [Pi.single_apply, eq_comm]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module (ZMod 2) (V i)]

/-- The square-value span on an actual subspace, before taking an annihilator. -/
def quadraticValueSpan {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range (fun u : U ↦ fun i ↦ q i ((e u.1).2 i)))

/-- Coefficient vectors of the actual annihilating kernel functionals. -/
def quadraticCoordinateAnnihilator {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) : Submodule (ZMod 2) (ι → ZMod 2) :=
  (quadraticValueSpan e q U).dualAnnihilator.map binaryDualCoordinates.toLinearMap

/-- Membership retains the equations for every vector of the actual U. -/
theorem mem_quadraticCoordinateAnnihilator {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) (b : ι → ZMod 2) :
    b ∈ quadraticCoordinateAnnihilator e q U ↔
      ∀ u : U, ∑ i, b i * q i ((e u.1).2 i) = 0 := by
  constructor
  · rintro ⟨f, hf, rfl⟩ u
    have h := (Submodule.mem_dualAnnihilator f).mp hf
      (fun i ↦ q i ((e u.1).2 i)) (Submodule.subset_span (Set.mem_range_self u))
    simpa only [binaryDualCoordinates_eval] using h
  · intro h
    refine ⟨binaryDualCoordinates.symm b, ?_, binaryDualCoordinates.apply_symm_apply b⟩
    apply (Submodule.mem_dualAnnihilator _).mpr
    have hs : quadraticValueSpan e q U ≤ (binaryDualCoordinates.symm b).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨u, rfl⟩
      change binaryDualCoordinates.symm b (fun i ↦ q i ((e u.1).2 i)) = 0
      rw [binaryDualCoordinates_eval, binaryDualCoordinates.apply_symm_apply]
      exact h u
    intro v hv
    exact hs hv

/-- Full quadratic incidence uses the transported original annihilator,
with no replacement by its dimension. -/
theorem fullQuadraticSubspace_iff {R : ℕ}
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (B : Submodule (ZMod 2) (ι → ZMod 2))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) :
    FullQuadraticSubspace e B q U ↔
      (∀ i, Function.Surjective (fun u : U ↦ (e u.1).2 i)) ∧
        B ≤ quadraticCoordinateAnnihilator e q U := by
  constructor
  · rintro ⟨hf, hq⟩
    refine ⟨hf, fun b hb ↦ (mem_quadraticCoordinateAnnihilator e q U b).mpr ?_⟩
    exact hq ⟨b, hb⟩
  · rintro ⟨hf, hB⟩
    exact ⟨hf, fun b ↦ (mem_quadraticCoordinateAnnihilator e q U b.1).mp (hB b.2)⟩

omit [Fintype ι] in
/-- A pointwise original-square chart identifies the whole retained span
for every image. Surjectivity supplies every image vector, including zero. -/
theorem binaryImageSquareObstruction_eq_quadraticValueSpan
    {G : Type*} [Group G] {R : ℕ}
    (π : G →* Multiplicative (Fin R → ZMod 2)) (hπ : Function.Surjective π)
    (κ : Multiplicative (ι → ZMod 2) ≃* π.ker)
    (e : (Fin R → ZMod 2) ≃ₗ[ZMod 2] (W × ∀ i, V i))
    (q : ∀ i, QuadraticForm (ZMod 2) (V i))
    (hsq : ∀ g : G, binarySquareCoordinate π κ g =
      fun i ↦ q i ((e (π g).toAdd).2 i))
    (U : Submodule (ZMod 2) (Fin R → ZMod 2)) :
    binaryImageSquareObstruction π κ U = quadraticValueSpan e q U := by
  apply le_antisymm
  · apply (binaryImageSquareObstruction_le_iff π κ U _).mpr
    intro g hg
    rw [hsq]
    exact Submodule.subset_span (Set.mem_range_self (⟨(π g).toAdd, hg⟩ : U))
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    obtain ⟨g, hg⟩ := hπ (Multiplicative.ofAdd u.1)
    have hm : (π g).toAdd ∈ U := by simpa only [hg] using u.2
    have hmem := (binaryImageSquareObstruction_le_iff π κ U _).mp le_rfl g hm
    simpa only [hsq, hg] using hmem

end SymmetricSubgroupAsymptotics
