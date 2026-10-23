import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalTripleRootOperators
import SymmetricSubgroupAsymptotics.CFSGLinearMapImageParameterizedTripleProduct

/-! Independent parameters in the cubic image formula for ORIGINAL
Serre root operators. In particular the three parameters may be a,
a^q and a^(q^2); the theorem does not assert fixed-point membership or
a triality model comparison. The cubic composition is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped TensorProduct
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalParameterizedTriple
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoCoordinateImageDegreeTwo CFSGNormTwoCoordinateOriginalMixedOperators
open CFSGNormTwoCoordinateOriginalTripleRootOperators
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀
local notation "C" => CFSGGeckSerreRepresentation.cartan b₀ s₀

theorem mapped_original_parameterized_triple (K : Type) [Field K]
    (neg : Bool) (u : Fin 3→Fin r)
    (horth : ∀ i j : Fin 3, i≠j→integerPairing A (s₀ (u i):Roots A).val (s₀ (u j):Roots A).val=0)
    (t : Fin 3→K) (x : Space C K) :
    let P : Fin 3→Module.End K (Space C K):=fun i=>originalCoefficient A hd hs hp ho K neg (u i) 1
    let Q : Fin 3→Module.End K (Space C K):=fun i=>originalCoefficient A hd hs hp ho K neg (u i) 2
    baseChange D K (rootOperator C K neg (u 0) (t 0)
      (rootOperator C K neg (u 1) (t 1) (rootOperator C K neg (u 2) (t 2) x)))=
      baseChange D K x+(t 0 • baseChange D K (P 0 x)+t 1 • baseChange D K (P 1 x)+t 2 • baseChange D K (P 2 x))+
      ((t 0)^2 • baseChange D K (Q 0 x)+(t 1)^2 • baseChange D K (Q 1 x)+(t 2)^2 • baseChange D K (Q 2 x)+
        (t 0*t 1) • baseChange D K (P 0 (P 1 x))+(t 0*t 2) • baseChange D K (P 0 (P 2 x))+
        (t 1*t 2) • baseChange D K (P 1 (P 2 x)))+
      (t 0*t 1*t 2) • baseChange D K (P 0 (P 1 (P 2 x))) := by
  dsimp only
  let P : Fin 3→Module.End K (Space C K):=fun i=>originalCoefficient A hd hs hp ho K neg (u i) 1
  let Q : Fin 3→Module.End K (Space C K):=fun i=>originalCoefficient A hd hs hp ho K neg (u i) 2
  let R : Fin 3→Module.End K (Space C K):=fun i=>rootOperator C K neg (u i) (t i)
  let T := fun i : Fin 3=>CFSGIntegralQuadraticRootOperators.operator K
    (fieldRoot D K neg (u i)) (fieldSecond D K neg (u i)) 1
  let U := fun i : Fin 3=>CFSGIntegralQuadraticRootOperators.operator K
    (fieldRoot D K neg (u i)) (fieldSecond D K neg (u i)) 2
  have hP (i : Fin 3) (y : Space C K) : baseChange D K (P i y)=T i (baseChange D K y) :=
    baseChange_operator D K neg (u i) 1 y
  have hQ (i : Fin 3) (y : Space C K) : baseChange D K (Q i y)=U i (baseChange D K y) :=
    baseChange_operator D K neg (u i) 2 y
  have hpq (i j : Fin 3) (hij : i≠j) (y : Space C K) : baseChange D K (P i (Q j y))=0 :=
    all_ring_original_mixed_zero A hd hs hp ho K neg (u i) (u j) (horth i j hij)
      1 2 (Or.inr (Or.inl ⟨rfl,rfl⟩)) y
  have hqp (i j : Fin 3) (hij : i≠j) (y : Space C K) : baseChange D K (Q i (P j y))=0 :=
    all_ring_original_mixed_zero A hd hs hp ho K neg (u i) (u j) (horth i j hij)
      2 1 (Or.inl ⟨rfl,rfl⟩) y
  have hqq (i j : Fin 3) (hij : i≠j) (y : Space C K) : baseChange D K (Q i (Q j y))=0 :=
    all_ring_original_mixed_zero A hd hs hp ho K neg (u i) (u j) (horth i j hij)
      2 2 (Or.inr (Or.inr ⟨rfl,rfl⟩)) y
  have hR (i : Fin 3) (y : Space C K) :
      baseChange D K (R i y)=baseChange D K y+t i • baseChange D K (P i y)+
        (t i)^2 • baseChange D K (Q i y) := by
    have hh:=original_rootOperator_degree_two A hd hs hp ho K neg (u i) (t i) y
    rw [←baseChange_operator D K neg (u i) 1 y,←baseChange_operator D K neg (u i) 2 y] at hh
    exact hh
  exact CFSGLinearMapImageParameterizedTripleProduct.mapped_product_three (baseChange D K)
    P Q R T U hP hQ hpq hqp hqq t hR x

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalParameterizedTriple
