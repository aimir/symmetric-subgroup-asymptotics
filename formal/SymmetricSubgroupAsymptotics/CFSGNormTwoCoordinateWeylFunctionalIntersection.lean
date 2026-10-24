import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylIntersectionCardinality
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateZeroFunctionalSupport

/-! A genuine Weyl inversion intersection is supported on the zero
roots of a functional whenever each of its inversion roots is zero.
The conclusion uses actual sign-part generation, not an assumed chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylFunctionalIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylIntersectionFactor CFSGNormTwoCoordinateWeylIntersectionCardinality
open CFSGNormTwoCoordinateZeroFunctionalSupport CFSGSerreQuadraticWeylWord
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem inversion_le_zeroFunctionalGroup (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (f : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (hf : ∀ k : PositiveRoot A,
      (¬∀ j,0≤(wordRoot A hs hp b₀ s₀ w k.val).val j) → f k.val.val=0) :
    rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K true).comap
        (MulAut.conj (canonicalWord D K w)).toMonoidHom ≤
      zeroFunctionalGroup A hd hs hp ho K f := by
  intro x hx
  let u : PositiveGroup A hd hs hp ho K := ⟨x,hx.1⟩
  have hu : u ∈ wordSignPart A hd hs hp ho K w true := hx.2
  rw [←signRootGroup_eq_part A hd hs hp ho K w true] at hu
  have hle : signRootGroup A hd hs hp ho K w true ≤
      (zeroFunctionalGroup A hd hs hp ho K f).comap
        (PositiveGroup A hd hs hp ho K).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k,a,rfl⟩
    have hk : ¬∀ j,0≤(wordRoot A hs hp b₀ s₀ w k.val.val).val j := by
      simpa only [signRoots,if_true,Finset.mem_filter,Finset.mem_univ,true_and] using k.property
    exact root_mem_zeroFunctionalGroup A hd hs hp ho K f k.val (hf k.val hk) a.toAdd
  exact hle hu

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylFunctionalIntersection
