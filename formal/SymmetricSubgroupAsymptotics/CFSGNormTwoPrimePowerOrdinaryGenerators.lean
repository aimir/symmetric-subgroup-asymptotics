import SymmetricSubgroupAsymptotics.CFSGNormTwoOriginalOrdinaryGenerators
import SymmetricSubgroupAsymptotics.External.CFSG.Parameters

/-! The exact pinned-field exponent in the actual original ordinary
root-generator bound. Matrix transport uses an explicit Cartan equality;
no identification of a natural matrix model is inferred here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoPrimePowerOrdinaryGenerators
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀ i, A i i = 2)
    (hs : A.transpose = A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀ i j, i ≠ j → A i j ≤ 0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    (q : CFSG.PrimePower)
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem genRank_le_twice_rank_mul_exponent
    [IsSimpleGroup (Projective (cartan b₀ s₀) q.Field)] (i : Fin r) :
    MarkedC4.genRank (Projective (cartan b₀ s₀) q.Field) ≤ (2*r)*q.exponent := by
  have hh := CFSGNormTwoOriginalOrdinaryGenerators.genRank_le_twice_rank_mul_finrank
    A hd hs hp ho q.Field i q.prime
  have he : Module.finrank (ZMod q.prime) q.Field = q.exponent :=
    GaloisField.finrank q.prime (Nat.ne_of_gt q.exponent_pos)
  simpa only [he] using hh

theorem exists_generating_finset
    [IsSimpleGroup (Projective (cartan b₀ s₀) q.Field)] (i : Fin r) :
    ∃ S : Finset (Projective (cartan b₀ s₀) q.Field),
      Subgroup.closure (S : Set (Projective (cartan b₀ s₀) q.Field)) = ⊤ ∧
        S.card ≤ (2*r)*q.exponent := by
  have hh := CFSGNormTwoOriginalOrdinaryGenerators.exists_generating_finset
    A hd hs hp ho q.Field i q.prime
  have he : Module.finrank (ZMod q.prime) q.Field = q.exponent :=
    GaloisField.finrank q.prime (Nat.ne_of_gt q.exponent_pos)
  simpa only [he] using hh

theorem genRank_le_of_cartan_eq {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : cartan b₀ s₀ = C) [IsSimpleGroup (Projective C q.Field)] (i : Fin r) :
    MarkedC4.genRank (Projective C q.Field) ≤ (2*r)*q.exponent := by
  subst C
  exact genRank_le_twice_rank_mul_exponent A hd hs hp ho q i

theorem exists_generating_finset_of_cartan_eq {C : Matrix (Fin r) (Fin r) ℤ}
    (hC : cartan b₀ s₀ = C) [IsSimpleGroup (Projective C q.Field)] (i : Fin r) :
    ∃ S : Finset (Projective C q.Field),
      Subgroup.closure (S : Set (Projective C q.Field)) = ⊤ ∧
        S.card ≤ (2*r)*q.exponent := by
  subst C
  exact exists_generating_finset A hd hs hp ho q i

end SymmetricSubgroupAsymptotics.CFSGNormTwoPrimePowerOrdinaryGenerators
