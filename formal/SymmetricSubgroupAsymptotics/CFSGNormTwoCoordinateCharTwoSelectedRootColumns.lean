import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoRootWordSteps
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear

/-! The selected-root step uses the original target root labels, rather
than requiring a computed inverse of the noncomputably chosen rootWitness
word. Its inverse labels and the root-sum equation are derived through
the actual integral Weyl linear equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoSelectedRootColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylWordAlgebra CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoCoordinateRootSubgroup CFSGNormTwoCoordinateSelectedRootElement
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i=2)
  (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef) (ho : ∀ i j, i≠j → A i j≤0)
  [Fintype (Roots A)] [DecidableEq (Roots A)]
  [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho
private abbrev Mat (K : Type) := Matrix ((b₀).support⊕Roots A) ((b₀).support⊕Roots A) K

omit [(rootPairing A hs hp).IsReduced] in
private theorem inverse_word_root_apply (w : List (Fin r)) (k : Roots A) :
    wordRoot A hs hp b₀ s₀ w (wordRoot A hs hp b₀ s₀ (inverseWord w) k)=k := by
  apply Subtype.ext
  rw [←wordLinear_root,←wordLinear_root,wordLinear_inverseWord]
  exact (wordLinear A hs hp b₀ s₀ w).apply_symm_apply k.val

private theorem witness_simple_image (beta : Roots A) :
    wordRoot A hs hp b₀ s₀ (rootWitness A hd hs hp ho beta).val.1
      (s₀ (rootWitness A hd hs hp ho beta).val.2) = negativeIndex A hs hp beta := by
  let z := rootWitness A hd hs hp ho beta
  have hn : wordRoot A hs hp b₀ s₀ z.val.1 (negativeIndex A hs hp (s₀ z.val.2))=beta := by
    apply Subtype.ext
    rw [←wordLinear_root,CFSGNormTwoGeckColumns.negative_val]
    exact z.property.symm
  apply Subtype.ext
  calc
    _ = -(wordRoot A hs hp b₀ s₀ z.val.1
        (negativeIndex A hs hp (s₀ z.val.2))).val := by
      rw [wordRoot_negative_val,neg_neg]
    _ = -beta.val := congrArg (fun k : Roots A => -k.val) hn
    _ = (negativeIndex A hs hp beta).val := (CFSGNormTwoGeckColumns.negative_val A hs hp beta).symm

theorem selected_root_add (K : Type) [Field K] [CharP K 2] (beta gamma eta : Roots A)
    (hopp : gamma≠negativeIndex A hs hp beta) (hsum : eta.val=beta.val+gamma.val) (t : K) :
    (selectedRootElement A hd hs hp ho K beta t : Mat A hd hs hp ho K) *ᵥ
      Pi.single (.inr gamma) 1 = Pi.single (.inr gamma) 1+t • Pi.single (.inr eta) 1 := by
  let z := rootWitness A hd hs hp ho beta
  let w := z.val.1
  let i := z.val.2
  let j := wordRoot A hs hp b₀ s₀ (inverseWord w) gamma
  let k := wordRoot A hs hp b₀ s₀ (inverseWord w) eta
  have hjgamma : wordRoot A hs hp b₀ s₀ w j=gamma := inverse_word_root_apply A hd hs hp ho w gamma
  have hketa : wordRoot A hs hp b₀ s₀ w k=eta := inverse_word_root_apply A hd hs hp ho w eta
  have hsimple : wordRoot A hs hp b₀ s₀ w (s₀ i)=negativeIndex A hs hp beta :=
    witness_simple_image A hd hs hp ho beta
  have hj : j≠(s₀ i : Roots A) := by
    intro he
    exact hopp ((hjgamma.symm.trans (congrArg (wordRoot A hs hp b₀ s₀ w) he)).trans hsimple)
  have hint : k.val+(s₀ i : Roots A).val=j.val := by
    apply (wordLinear A hs hp b₀ s₀ w).injective
    calc
      _ = (wordRoot A hs hp b₀ s₀ w k).val+
          (wordRoot A hs hp b₀ s₀ w (s₀ i)).val := by
        rw [map_add,wordLinear_root,wordLinear_root]
      _ = eta.val+(negativeIndex A hs hp beta).val :=
        congrArg₂ (fun a b : Roots A => a.val+b.val) hketa hsimple
      _ = eta.val+(-beta.val) :=
        congrArg (fun v => eta.val+v) (CFSGNormTwoGeckColumns.negative_val A hs hp beta)
      _ = gamma.val := by rw [hsum]; abel
      _ = wordLinear A hs hp b₀ s₀ w j.val := by rw [wordLinear_root,hjgamma]
  have hroot : (rootPairing A hs hp).root k+(rootPairing A hs hp).root (s₀ i) =
      (rootPairing A hs hp).root j := by
    change castVector k.val+castVector (s₀ i : Roots A).val=castVector j.val
    ext n
    have hh := congrFun hint n
    change (k.val n : ℚ)+((s₀ i : Roots A).val n : ℚ)=(j.val n : ℚ)
    exact_mod_cast hh
  have ht := CFSGNormTwoCoordinateCharTwoRootWordSteps.selected_add_step
    A hd hs hp ho K beta j k hj hroot t
  change (selectedRootElement A hd hs hp ho K beta t : Mat A hd hs hp ho K) *ᵥ
      Pi.single (.inr (wordRoot A hs hp b₀ s₀ w j)) 1 =
      Pi.single (.inr (wordRoot A hs hp b₀ s₀ w j)) 1+
        t • Pi.single (.inr (wordRoot A hs hp b₀ s₀ w k)) 1 at ht
  rw [hjgamma,hketa] at ht
  exact ht

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateCharTwoSelectedRootColumns
