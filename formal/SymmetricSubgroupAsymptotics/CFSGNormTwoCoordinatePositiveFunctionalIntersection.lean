import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWeylFunctionalIntersection

/-! The genuine positive Weyl remainder lies in a functional tail when
every root remaining positive has the stated positive functional height.
This uses the checked sign-part generation, not an assumed coordinate
chart or fixed-point section surjectivity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveFunctionalIntersection
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckPositivePGroup
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoCoordinateWeylIntersectionFactor CFSGNormTwoCoordinateWeylIntersectionCardinality
open CFSGNormTwoCoordinateFunctionalRootTail CFSGSerreQuadraticWeylWord
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem positive_intersection_le_functionalTail (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (f : (Fin r → ℤ) →ₗ[ℤ] ℤ) (n : ℤ)
    (hf : ∀ k : PositiveRoot A,
      (∀ j,0≤(wordRoot A hs hp b₀ s₀ w k.val).val j) → n ≤ f k.val.val) :
    rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K false).comap
        (MulAut.conj (canonicalWord D K w)).toMonoidHom ≤
      functionalTail A hd hs hp ho K f n := by
  intro x hx
  let u : PositiveGroup A hd hs hp ho K := ⟨x,hx.1⟩
  have hu : u ∈ wordSignPart A hd hs hp ho K w false := hx.2
  rw [← signRootGroup_eq_part A hd hs hp ho K w false] at hu
  have hle : signRootGroup A hd hs hp ho K w false ≤
      (functionalTail A hd hs hp ho K f n).comap
        (PositiveGroup A hd hs hp ho K).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨k,a,rfl⟩
    have hk : ∀ j,0≤(wordRoot A hs hp b₀ s₀ w k.val.val).val j := by
      simpa only [signRoots,Bool.false_eq_true,if_false,Finset.mem_filter,
        Finset.mem_univ,true_and] using k.property
    exact root_mem_functionalTail A hd hs hp ho K f n k.val.val k.val.property
      (hf k.val hk) a.toAdd
  exact hle hu

theorem positive_intersection_le_strict (K : Type) [Field K] [Finite K]
    (w : List (Fin r)) (f : (Fin r → ℤ) →ₗ[ℤ] ℤ)
    (hf : ∀ k : PositiveRoot A,
      (∀ j,0≤(wordRoot A hs hp b₀ s₀ w k.val).val j) → 1 ≤ f k.val.val) :
    rootGroup A hs hp b₀ s₀ K false ⊓
      (rootGroup A hs hp b₀ s₀ K false).comap
        (MulAut.conj (canonicalWord D K w)).toMonoidHom ≤
      CFSGGradedMatrixSubgroups.strictUnits (fun j => f (CFSGNormTwoGeckLatticeDegree.latticeWeight A hs hp b₀ j)) :=
  (positive_intersection_le_functionalTail A hd hs hp ho K w f 1 hf).trans
    (functionalTail_le_strict A hd hs hp ho K f 1 (by decide))

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveFunctionalIntersection
