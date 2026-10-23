import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootStarHom
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarRootActions
import SymmetricSubgroupAsymptotics.CFSGAdditiveParameterConjugation

/-! Actual forward elementary row conjugators on the full exceptional
chain-star chart. The primitive integral A2 coefficient is rescaled by
its proved unit sign. Equality on the whole additive star follows from
its literal one-coordinate generators. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarForwardRows
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGSerreQuadraticMatrix
open CFSGExceptionalChainStarData CFSGNormTwoCoordinateRootStarHom
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinateSelectedRootAdditive
open CFSGNormTwoCoordinatePositivePairCommute CFSGNormTwoCoordinateChainStarRootActions
open CFSGNormTwoCoordinateRootCollectingTransport CFSGNormTwoGeckIntegralRealization
open CFSGAdditiveParameterConjugation CFSGTypeAElementaryMatrices

private theorem parameter_add {V M:Type*} [AddGroup V] [Group M]
    (f:Multiplicative V→*M) (v w:V) :
    f (Multiplicative.ofAdd (v+w))=f (Multiplicative.ofAdd v)*f (Multiplicative.ofAdd w) :=
  f.map_mul _ _

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (K : Type) [Field K]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
local notation "D" => realizationData A hs hp b₀ s₀

theorem rawHom_single {m : ℕ} (f : Fin m→CFSGNormTwoCoordinatePositiveRootGenerators.PositiveRoot A)
    (hpair : ∀i j,i≠j→integerPairing A (f i).val.val (f j).val.val=1)
    (i : Fin m) (a : K) :
    rawHom A hd hs hp ho K f hpair (Multiplicative.ofAdd (Pi.single i a))=
      selectedRootElement A hd hs hp ho K (f i).val a := by
  let hc : Pairwise (fun j k=>∀b c:Multiplicative K,
      Commute (selectedRootHom A hd hs hp ho K (f j).val b)
        (selectedRootHom A hd hs hp ho K (f k).val c)) := by
    intro j k hjk b c
    exact positive_pair_commute A hd hs hp ho K (f j).val (f k).val
      (f j).property (f k).property (Or.inr (hpair j k hjk)) b.toAdd c.toAdd
  change MonoidHom.noncommPiCoprod (fun j=>selectedRootHom A hd hs hp ho K (f j).val) hc
    (fun j=>Multiplicative.ofAdd ((Pi.single i a : Fin m→K) j))=_
  have he : (fun j=>Multiplicative.ofAdd ((Pi.single i a : Fin m→K) j))=
      (Pi.mulSingle i (Multiplicative.ofAdd a) : Fin m→Multiplicative K) := by
    ext j
    by_cases hj:j=i
    · subst j
      rw [Pi.single_eq_same,Pi.mulSingle_eq_same]
    · rw [Pi.single_eq_of_ne hj,Pi.mulSingle_eq_of_ne hj]
      rfl
  rw [he,MonoidHom.noncommPiCoprod_mulSingle]
  rfl

theorem forward_row {n : ℕ} (C : ChainStar A n) (j : Fin n) (a : K) :
    ∃t:K,∀v:Fin (n+1)→K,
      canonicalRoot D K false (C.step j) t*
        rawHom A hd hs hp ho K C.root C.pair (Multiplicative.ofAdd v)*
        (canonicalRoot D K false (C.step j) t)⁻¹=
      rawHom A hd hs hp ho K C.root C.pair
        (Multiplicative.ofAdd ((elementary (by
          intro he
          have hv := congrArg Fin.val he
          simp only [Fin.val_succ,Fin.val_castSucc] at hv
          omega : j.succ≠j.castSucc) a).toLin' v)) := by
  let hij : j.succ≠j.castSucc := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_succ,Fin.val_castSucc] at hv
    omega
  obtain ⟨ε,hε,he⟩ := forward_commutator_sign A hd hs hp ho C j
  refine ⟨(ε:K)*a,?_⟩
  intro v
  apply conjugation_of_single (rawHom A hd hs hp ho K C.root C.pair)
    (elementary hij a).toLin'.toAddEquiv
  intro k b
  change _=rawHom A hd hs hp ho K C.root C.pair
    (Multiplicative.ofAdd ((elementary hij a).toLin' (Pi.single k b)))
  rw [rawHom_single A hd hs hp ho K C.root C.pair]
  by_cases hk:k=j.castSucc
  · subst k
    have hcoef : (ε:K)*(b*((ε:K)*a))=a*b := by
      rcases hε with rfl|rfl <;> norm_num <;> ring
    have hh := he K ((ε:K)*a) b
    rw [hcoef] at hh
    change canonicalRoot D K false (C.step j) ((ε:K)*a)*
      selectedRootElement A hd hs hp ho K (C.root j.castSucc).val b*
      (canonicalRoot D K false (C.step j) ((ε:K)*a))⁻¹*
      (selectedRootElement A hd hs hp ho K (C.root j.castSucc).val b)⁻¹=_ at hh
    have hconj := (mul_inv_eq_iff_eq_mul).mp hh
    rw [elementary_apply,Pi.single_eq_same]
    rw [parameter_add,rawHom_single,rawHom_single]
    rw [hconj]
    exact (positive_pair_commute A hd hs hp ho K (C.root j.succ).val (C.root j.castSucc).val
      (C.root j.succ).property (C.root j.castSucc).property
      (Or.inr (C.pair j.succ j.castSucc hij)) (a*b) b).eq
  · have hc := other_root_commutes A hd hs hp ho C K j k hk ((ε:K)*a) b
    rw [hc.eq,mul_assoc,mul_inv_cancel,mul_one]
    rw [elementary_apply,Pi.single_eq_of_ne (Ne.symm hk),mul_zero,Pi.single_zero,add_zero,
      rawHom_single]

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateChainStarForwardRows
