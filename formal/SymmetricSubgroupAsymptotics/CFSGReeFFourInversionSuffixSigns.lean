import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSignPilot

/-! The remaining five bounded integer suffix certificates. Every
certificate uses only six explicit root vectors in Z^6; the selected
length-zero/one/two pilot is reused without alteration. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSigns
open CFSGReeFFourInversionSuffixSignPilot CFSGReeFFourPositiveBlockConjugation
open CFSGNormTwoCoordinateLatticeWord CFSGNormTwoGeckWeylWordDegree
open CFSGSignedCartanReflections
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoRootPairing
open CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

private def vectorSigns (n : ℕ) : Prop :=
  ∀ b : Bool, ∀ r : Fin 6, ∀ j : Fin 6,
    0≤vectorWord (conjugatingWord b n ++ (blockRootPair b r).1)
      (Pi.single (blockRootPair b r).2 (1:ℤ)) j

private theorem signs_three : vectorSigns 3 := by
  unfold vectorSigns
  decide +kernel
private theorem signs_four : vectorSigns 4 := by
  unfold vectorSigns
  decide +kernel
private theorem signs_five : vectorSigns 5 := by
  unfold vectorSigns
  decide +kernel
private theorem signs_six : vectorSigns 6 := by
  unfold vectorSigns
  decide +kernel
private theorem signs_seven : vectorSigns 7 := by
  unfold vectorSigns
  decide +kernel

private theorem signs_of_vectors (n : ℕ) (hc : vectorSigns n) (b : Bool) :
    positiveBlockSigns b (conjugatingWord b n) := by
  have hindexed : blockRoots b ⊆ List.ofFn (blockRootPair b) := by
    cases b <;> decide +kernel
  intro w i hi j
  obtain ⟨r,hr⟩ := List.mem_ofFn.mp (hindexed hi)
  have he := LinearMap.congr_fun
    (latticeWord_linear A hd hs hp ho (conjugatingWord b n ++ w))
    (s₀ i : Roots A).val
  change latticeWord A (conjugatingWord b n ++ w)*ᵥ(Pi.single i (1:ℤ))=
    wordLinear A hs hp b₀ s₀ (conjugatingWord b n ++ w) (s₀ i : Roots A).val at he
  rw [wordLinear_root] at he
  rw [←he,←vectorWord_eq]
  have h := hc b r j
  rw [hr] at h
  exact h

theorem positiveBlockSigns_all_suffixes (b : Bool) (k : Fin 8) :
    positiveBlockSigns b (conjugatingWord b k.val) := by
  fin_cases k
  · exact positiveBlockSigns_first_three b ⟨0,by decide⟩
  · exact positiveBlockSigns_first_three b ⟨1,by decide⟩
  · exact positiveBlockSigns_first_three b ⟨2,by decide⟩
  · exact signs_of_vectors 3 signs_three b
  · exact signs_of_vectors 4 signs_four b
  · exact signs_of_vectors 5 signs_five b
  · exact signs_of_vectors 6 signs_six b
  · exact signs_of_vectors 7 signs_seven b

end SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSigns
