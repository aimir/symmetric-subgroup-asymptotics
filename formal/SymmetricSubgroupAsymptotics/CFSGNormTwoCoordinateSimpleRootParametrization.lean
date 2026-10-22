import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSelectedRootElement
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootWordIdentity
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSelfRootConjugation

/-! The selected element of an original positive SIMPLE root is the
actual canonical positive root element, up to an integer unit parameter.
The comparison is proved using the literal inverse Weyl word, with the
SAME sign over every coefficient ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoCoordinateRootSubgroup
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

theorem triple_word_negative_degree (i : Fin r) :
    wordLinear A hs hp b₀ s₀ [i,i,i] (-(s₀ i:Roots A).val)=(s₀ i:Roots A).val := by
  let R := reflectionEquiv A (s₀ i)
  have hpos : R (s₀ i:Roots A).val= -(s₀ i:Roots A).val := by
    change (s₀ i:Roots A).val-integerPairing A (s₀ i:Roots A).val (s₀ i:Roots A).val •
      (s₀ i:Roots A).val= -(s₀ i:Roots A).val
    rw [(s₀ i:Roots A).property]
    module
  have hneg : R (-(s₀ i:Roots A).val)=(s₀ i:Roots A).val := by
    rw [map_neg,hpos,neg_neg]
  change R (R (R (-(s₀ i:Roots A).val)))=(s₀ i:Roots A).val
  rw [hneg,hpos,hneg]

theorem canonical_triple_word_inverse (K : Type) [CommRing K] (i : Fin r) :
    canonicalWord D K [i,i,i]=(canonicalWeyl D K i)⁻¹ := by
  have hfour : (canonicalWeyl D K i)^4=1 := canonicalWeyl_four_of_rational D K i
    (CFSGNormTwoGeckWeylUnits.weyl_four A hs hp b₀ s₀ ℚ i)
  symm
  apply inv_eq_of_mul_eq_one_right
  calc
    _=(canonicalWeyl D K i)^4 := by
      simp only [canonicalWord,pow_succ,pow_zero,mul_one,one_mul,mul_assoc]
    _=1 := hfour

theorem triple_negative_word (K : Type) [CommRing K] (i : Fin r) (a : K) :
    rootWord D K [i,i,i] true i a=canonicalRoot D K false i (-a) := by
  rw [rootWord,canonical_triple_word_inverse,inv_inv]
  have hself := CFSGNormTwoGeckSelfRootConjugation.self_root_word A hs hp b₀ s₀ K i (-a)
  simp only [neg_neg] at hself
  calc
    _=(canonicalWeyl D K i)⁻¹*
        (canonicalWeyl D K i*canonicalRoot D K false i (-a)*(canonicalWeyl D K i)⁻¹)*
          canonicalWeyl D K i := congrArg
            (fun x=>(canonicalWeyl D K i)⁻¹*x*canonicalWeyl D K i) hself.symm
    _=_ := by group

theorem selected_simple_root_sign (i : Fin r) :
    ∃ε : ℤ,(ε=1 ∨ ε= -1) ∧ ∀(K : Type) [CommRing K] (a : K),
      selectedRootElement A hd hs hp ho K (s₀ i) a=canonicalRoot D K false i ((ε:K)*a) := by
  let p := rootWitness A hd hs hp ho (s₀ i)
  have hdegree : wordLinear A hs hp b₀ s₀ p.val.1 (-(s₀ p.val.2:Roots A).val)=
      wordLinear A hs hp b₀ s₀ [i,i,i] (-(s₀ i:Roots A).val) :=
    p.property.symm.trans (triple_word_negative_degree A hd hs hp ho i).symm
  obtain ⟨ε,hε,he⟩ := CFSGNormTwoCoordinateRootWordIdentity.same_degree_root_identity
    A hd hs hp ho p.val.1 [i,i,i] p.val.2 i hdegree
  refine ⟨-ε,?_,?_⟩
  · rcases hε with rfl|rfl <;> norm_num
  · intro K _ a
    change rootWord D K p.val.1 true p.val.2 a=canonicalRoot D K false i (((-ε:ℤ):K)*a)
    rw [he K a,triple_negative_word]
    simp only [Int.cast_neg,neg_mul]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootParametrization
