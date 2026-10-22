import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveNormalWordMembership

/-! Independent supported root parameters give genuine subgroup-cardinality
lower bounds inside actual U. The subgroup need only contain the specified
root factors; it need not have a presumed root factorization. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSupportCardinality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoCoordinateFinitePositiveNormalForm CFSGNormTwoCoordinatePositiveNormalWordMembership
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

def extendRootParameters (K : Type) [Zero K] (S : Finset (PositiveRoot A))
    (a : S→K) (k : PositiveRoot A) : K := by
  classical
  exact if hk : k∈S then a ⟨k,hk⟩ else 0

theorem extendRootParameters_injective (K : Type) [Zero K] (S : Finset (PositiveRoot A)) :
    Function.Injective (extendRootParameters A K S) := by
  classical
  intro a b he
  funext k
  have hh := congrArg (fun c : PositiveRoot A→K=>c k.val) he
  simpa only [extendRootParameters,dif_pos k.property] using hh

theorem root_support_card_le (K : Type) [Field K] [Finite K]
    (S : Finset (PositiveRoot A)) (H : Subgroup (PositiveGroup A hd hs hp ho K))
    (hS : ∀k : S,∀a : Multiplicative K,
      positiveRootParameterHom A hd hs hp ho K k.val.val k.val.property a∈H) :
    Nat.card K ^ S.card≤Nat.card H := by
  classical
  have hmem (a : S→K) :
      positiveRootNormalWord A hd hs hp ho K (extendRootParameters A K S a)∈H := by
    apply positiveRootNormalWord_mem_of_parameters A hd hs hp ho K H
    intro k
    by_cases hk : k∈S
    · simpa only [extendRootParameters,dif_pos hk] using hS ⟨k,hk⟩ (Multiplicative.ofAdd (a ⟨k,hk⟩))
    · have hz : extendRootParameters A K S a k=0 := dif_neg hk
      rw [hz]
      change positiveRootParameterHom A hd hs hp ho K k.val k.property 1∈H
      rw [map_one]
      exact H.one_mem
  let f : (S→K)→H := fun a=>⟨positiveRootNormalWord A hd hs hp ho K
    (extendRootParameters A K S a),hmem a⟩
  have hf : Function.Injective f := by
    intro a b he
    apply extendRootParameters_injective A K S
    apply (positiveRootNormalWord_bijective A hd hs hp ho K).1
    exact congrArg Subtype.val he
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_fun,Nat.card_eq_fintype_card (α:=S),Fintype.card_coe] using hc

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootSupportCardinality
