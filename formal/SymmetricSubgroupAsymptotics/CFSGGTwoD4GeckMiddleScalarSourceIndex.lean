import SymmetricSubgroupAsymptotics.CentralExtensionScalarWordIndex
import SymmetricSubgroupAsymptotics.CentralExtensionScalarPairingTransport
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarTorus

/-! The actual source normalizer realizes all scalar words on the entire
centre of its good-characteristic middle radical. The same central
intersection and join pay the scalar dual orbit and the vector bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarSourceIndex
open CFSGGTwoD4GeckMiddleSourceNormalizer CFSGGTwoD4GeckMiddleScalarTorus
open CFSGGTwoD4GeckMiddleCentralExtensionData ScalarCentrePrimeFieldAction
variable (K : Type) [Field K] [Finite K]

def sourceData (hthree : (3 : K) ≠ 0) :
    CentralExtensionScalarPairingIndex.Data (F := K) (V := Fin 4 → K) (N := radical K) :=
  CentralExtensionScalarPairingTransport.transport (extensionData K hthree) (radicalEquiv K)

def scalarAction (hthree : (3 : K) ≠ 0) :
    sourceNormalizer K →* MulAut (Multiplicative K) :=
  (scalarCentreAction (sourceData K hthree)).comp MulAut.conjNormal

theorem scalarAction_apply (hthree : (3 : K) ≠ 0) (g : sourceNormalizer K)
    (a : Multiplicative K) :
    (sourceData K hthree).central (scalarAction K hthree g a) =
      MulAut.conjNormal g ((sourceData K hthree).central a) :=
  scalarCentreAction_apply (sourceData K hthree) (MulAut.conjNormal g) a

theorem scalar_words (hthree : (3 : K) ≠ 0) (a : Kˣ) (b : K) :
    scalarAction K hthree (scalarTorus K a) (Multiplicative.ofAdd b) =
      Multiplicative.ofAdd ((a : K)*b) := by
  apply (sourceData K hthree).central_injective
  rw [scalarAction_apply]
  apply Subtype.ext
  apply Subtype.ext
  change (scalarTorus K a).val*(central K (Multiplicative.ofAdd b)).val*
    (scalarTorus K a).val⁻¹ = (central K (Multiplicative.ofAdd ((a : K)*b))).val
  exact scalarTorus_central_val K a b

def highestElement : sourceNormalizer K :=
  ((radicalEquiv K).symm (central K (Multiplicative.ofAdd (1 : K)))).val

theorem source_index_le_of_highest_motion (hthree : (3 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (M : Subgroup (sourceNormalizer K)) (hM : highestElement K ∉ M) :
    Nat.card K^2*(Nat.card K-1) ≤ M.index :=
  CentralExtensionScalarWordIndex.index_le_of_scalar_words (radical K) (sourceData K hthree)
    p 2 (by simp only [Module.finrank_fintype_fun_eq_card,Fintype.card_fin])
    (scalarAction K hthree) (scalarAction_apply K hthree)
    (fun a => ⟨scalarTorus K a,scalar_words K hthree a⟩) M hM

theorem degree_le_of_highest_motion (hthree : (3 : K) ≠ 0)
    (p : ℕ) [Fact p.Prime] [CharP K p]
    {X : Type*} [Finite X] [MulAction (sourceNormalizer K) X]
    (x : X) (hx : highestElement K • x ≠ x) :
    Nat.card K^2*(Nat.card K-1) ≤ Nat.card X := by
  calc
    _ ≤ (MulAction.stabilizer (sourceNormalizer K) x).index :=
      source_index_le_of_highest_motion K hthree p _ hx
    _ = (MulAction.orbit (sourceNormalizer K) x).ncard := MulAction.index_stabilizer _ _
    _ ≤ Nat.card X := Set.ncard_le_card _

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckMiddleScalarSourceIndex
