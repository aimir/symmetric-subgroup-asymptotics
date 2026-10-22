import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordIdentity
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylWordAlgebra

/-! Actual Weyl-word conjugation transports selected root elements with
an integer unit parameter change. The SAME sign works over every ring;
the original integer reflection word determines the target root. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoCoordinateRootSubgroup
open CFSGSerreQuadraticWeylWord CFSGSerreQuadraticWordRootTransport
open CFSGNormTwoCoordinateSelectedRootElement
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem canonicalWord_append (K : Type) [CommRing K] (u w : List (Fin r)) :
    canonicalWord D K (u++w)=canonicalWord D K u*canonicalWord D K w := by
  induction u with
  | nil=>simp only [List.nil_append,canonicalWord,one_mul]
  | cons i u ih=>rw [List.cons_append,canonicalWord,ih,canonicalWord,mul_assoc]

theorem word_selected_root_sign (u : List (Fin r)) (k : Roots A) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K : Type) [CommRing K] (a : K),
      canonicalWord D K u*selectedRootElement A hd hs hp ho K k a*(canonicalWord D K u)⁻¹=
        selectedRootElement A hd hs hp ho K (wordRoot A hs hp b₀ s₀ u k) ((ε:K)*a) := by
  let p := rootWitness A hd hs hp ho k
  let g := wordRoot A hs hp b₀ s₀ u k
  let q := rootWitness A hd hs hp ho g
  have hdegree : wordLinear A hs hp b₀ s₀ (u++p.val.1) (-(s₀ p.val.2:Roots A).val)=
      wordLinear A hs hp b₀ s₀ q.val.1 (-(s₀ q.val.2:Roots A).val) := by
    calc
      _=wordLinear A hs hp b₀ s₀ u
          (wordLinear A hs hp b₀ s₀ p.val.1 (-(s₀ p.val.2:Roots A).val)) := by
            rw [wordLinear_append];rfl
      _=wordLinear A hs hp b₀ s₀ u k.val := congrArg (wordLinear A hs hp b₀ s₀ u) p.property.symm
      _=g.val := wordLinear_root A hs hp b₀ s₀ u k
      _=_ := q.property
  obtain ⟨ε,hε,he⟩ := CFSGNormTwoCoordinateRootWordIdentity.same_degree_root_identity
    A hd hs hp ho (u++p.val.1) q.val.1 p.val.2 q.val.2 hdegree
  refine ⟨ε,hε,?_⟩
  intro K _ a
  have hw : canonicalWord D K u*selectedRootElement A hd hs hp ho K k a*(canonicalWord D K u)⁻¹=
      rootWord D K (u++p.val.1) true p.val.2 a := by
    rw [rootWord,canonicalWord_append]
    dsimp only [p,selectedRootElement,rootWord]
    group
  exact hw.trans (he K a)

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateWordRootElementSign
