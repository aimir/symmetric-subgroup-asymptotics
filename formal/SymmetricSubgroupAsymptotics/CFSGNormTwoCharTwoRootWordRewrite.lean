import SymmetricSubgroupAsymptotics.TwoLetterWordRewrite
import SymmetricSubgroupAsymptotics.CFSGNormTwoCharTwoRootWordCollectionStep

/-! Arithmetic validation of syntactic root-word rules, followed by actual
selected-root semantics. Every raised label must be the literal sum of the
same roots in the checked Chevalley relation. No collected normal form,
exceptional fixedness or derived membership is an input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCharTwoRootWordRewrite
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinatePositivePairCollecting
open CFSGNormTwoCharTwoRootWordCollectionStep TwoLetterWordRewrite
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    {I : Type*} (R : I → Roots A)

def validRule : Rule I → Prop
  | .cancel _ => True
  | .swap a b => integerPairing A (R b).val (R a).val = 0 ∨
      integerPairing A (R b).val (R a).val = 1
  | .raise a b c => integerPairing A (R b).val (R a).val = -1 ∧
      ∀ t : Fin r, (R c).val t = (R a).val t+(R b).val t

instance validRule_decidable (s : Rule I) : Decidable (validRule A R s) := by
  cases s <;> dsimp only [validRule] <;> infer_instance

variable (K : Type) [CommRing K] [CharP K 2]

abbrev parameter (i : I) := selectedRootElement A hd hs hp ho K (R i) 1

theorem rule_sound (hpos : ∀ i : I, ∀ t : Fin r, 0≤(R i).val t)
    (s : Rule I) (h : validRule A R s) :
    value (parameter A hd hs hp ho R K) s.before =
      value (parameter A hd hs hp ho R K) s.after := by
  cases s with
  | cancel a =>
    simpa only [Rule.before,Rule.after,value,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one] using root_cancel A hd hs hp ho K (R a)
  | swap a b =>
    simpa only [Rule.before,Rule.after,value,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one] using
        commuting_swap A hd hs hp ho K (R b) (R a) h
  | raise a b c =>
    rcases h with ⟨hpair,hc⟩
    have he : sumRoot A hs (R b) (R a) hpair = R c := by
      apply Subtype.ext
      funext t
      change (R b).val t+(R a).val t=(R c).val t
      rw [hc t,add_comm]
    have hh := adjacent_swap A hd hs hp ho K (R b) (R a)
      (hpos b) (hpos a) hpair
    rw [he] at hh
    simpa only [Rule.before,Rule.after,value,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh

theorem run_sound [DecidableEq I]
    (hpos : ∀ i : I, ∀ t : Fin r, 0≤(R i).val t)
    (steps : List (Step I)) (w w' : List I)
    (hrules : ∀ s ∈ steps, validRule A R s.rule)
    (h : TwoLetterWordRewrite.run steps w = some w') :
    value (parameter A hd hs hp ho R K) w = value (parameter A hd hs hp ho R K) w' :=
  TwoLetterWordRewrite.run_sound (parameter A hd hs hp ho R K) steps w w'
    (fun s hmem => rule_sound A hd hs hp ho R K hpos s.rule (hrules s hmem)) h

end SymmetricSubgroupAsymptotics.CFSGNormTwoCharTwoRootWordRewrite
