import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateDominantSupport
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds
import SymmetricSubgroupAsymptotics.CFSGIntegerPairingPositiveDescent

/-! In rank at least two, the actual dominant root has a simple coroot
pairing ONE. Thus its full field-unit character is available, including
in bad characteristic, without an exponent-surjectivity assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRootUnitCharacter
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoPairingBounds
open CFSGNormTwoCoordinateDominantSupport CFSGIntegerPairingPositiveDescent
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

include hd hs hp ho
theorem dominant_root_has_unit_simple_pairing [Nontrivial (Fin r)] (θ : Roots A)
    (hθ : ∀i,0≤θ.val i)
    (hdom : ∀i,0 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ)) :
    ∃i : Fin r,integerPairing A (s₀ i : Roots A).val θ.val=1 := by
  have hfull := dominant_positive_root_full_support A hd hs hp ho θ hθ hdom
  obtain ⟨i,hi,hpi⟩ := exists_positive_coordinate_pairing (integerPairing A) θ.val hθ
    (by rw [θ.property];decide)
  have hne : θ≠(s₀ i : Roots A) := by
    intro he
    obtain ⟨j,hj⟩ := exists_ne i
    have hz := congrArg (fun k : Roots A=>k.val j) he
    change θ.val j=(Pi.single i (1:ℤ) : Fin r→ℤ) j at hz
    simp [Pi.single_apply,Ne.symm hj] at hz
    have hpj := hfull j
    omega
  have hb : -2 ≤ integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ) ∧
      integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ)≤2 :=
    root_pairing_bounds A hs hp θ (s₀ i)
  have htwo : integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ)≠2 :=
    fun h=>hne ((root_pairing_eq_two_iff A hs hp θ (s₀ i)).mp h)
  refine ⟨i,?_⟩
  rw [integer_symmetric A hs (s₀ i : Roots A).val θ.val]
  change integerPairing A θ.val (Pi.single i (1:ℤ) : Fin r→ℤ)=1
  omega

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHighestRootUnitCharacter
