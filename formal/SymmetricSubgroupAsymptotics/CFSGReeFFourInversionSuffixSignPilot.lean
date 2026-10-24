import SymmetricSubgroupAsymptotics.CFSGReeFFourPositiveBlockConjugation
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateLatticeWord

/-! A selected integer sign pilot for the first three inverse suffixes.
Only six-dimensional integer vectors are evaluated, with no root-type
census or coefficient-field calculation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSignPilot
open CFSGReeFFourPositiveBlockConjugation CFSGSignedCartanReflections
open CFSGNormTwoCoordinateLatticeWord CFSGNormTwoGeckWeylWordDegree
open CFSGNormTwoGeckWeylLatticeLinear
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def simpleRawWord (middle : Bool) : List (Fin 6) :=
  if middle then [2,4,3,2,4,3] else [0,5,1]

def conjugatingWord (middle : Bool) : ℕ → List (Fin 6)
  | 0 => []
  | n+1 => simpleRawWord (if n%2=0 then !middle else middle) ++ conjugatingWord middle n

def blockRootPair (middle : Bool) (i : Fin 6) : List (Fin 6) × Fin 6 :=
  if middle then ![([],2),([],4),([],3),([2,4],3),([3],2),([3],4)] i
  else ![([],0),([],5),([],1),([],0),([],5),([],1)] i

def vectorWord : List (Fin 6) → (Fin 6 → ℤ) → (Fin 6 → ℤ)
  | [],x => x
  | i::w,x => latticeStep A i *ᵥ vectorWord w x

theorem vectorWord_eq (w : List (Fin 6)) (x : Fin 6 → ℤ) :
    vectorWord w x=latticeWord A w *ᵥ x := by
  induction w with
  | nil => simp only [vectorWord,latticeWord,Matrix.one_mulVec]
  | cons i w ih =>
    rw [vectorWord,latticeWord,ih,Matrix.mulVec_mulVec]

private theorem block_roots_indexed (b : Bool) :
    blockRoots b ⊆ List.ofFn (blockRootPair b) := by
  cases b <;> decide +kernel

private theorem selected_sign_certificate :
    ∀ b : Bool, ∀ k : Fin 3, ∀ r : Fin 6, ∀ j : Fin 6,
      0≤vectorWord (conjugatingWord b k.val ++ (blockRootPair b r).1)
        (Pi.single (blockRootPair b r).2 (1:ℤ)) j := by
  decide +kernel

theorem positiveBlockSigns_first_three (b : Bool) (k : Fin 3) :
    positiveBlockSigns b (conjugatingWord b k.val) := by
  intro w i hi j
  obtain ⟨r,hr⟩ := List.mem_ofFn.mp (block_roots_indexed b hi)
  have he := LinearMap.congr_fun
    (latticeWord_linear A hd hs hp ho (conjugatingWord b k.val ++ w))
    (s₀ i : Roots A).val
  change latticeWord A (conjugatingWord b k.val ++ w)*ᵥ(Pi.single i (1:ℤ))=
    wordLinear A hs hp b₀ s₀ (conjugatingWord b k.val ++ w) (s₀ i : Roots A).val at he
  rw [wordLinear_root] at he
  rw [←he,←vectorWord_eq]
  have hc := selected_sign_certificate b k r j
  rw [hr] at hc
  exact hc

end SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSignPilot
