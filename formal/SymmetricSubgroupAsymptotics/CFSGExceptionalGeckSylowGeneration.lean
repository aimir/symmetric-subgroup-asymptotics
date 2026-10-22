import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOriginalSylowGeneration
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeight
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! Actual defining-prime two-conjugate-Sylow generation for the original
simple E6/E7/E8 models. Soluble Sylow normalizers are NOT asserted here. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalGeckSylowGeneration
open CFSG.Models.Chevalley CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormTwoBases CFSGExceptionalGeckIntegralData
open CFSGNormTwoGeckOriginalSylowGeneration

local instance exceptionalGeckSylowE6DecEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance exceptionalGeckSylowE7DecEq : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance exceptionalGeckSylowE8DecEq : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

theorem serreTypeE6_two_conjugate_sylows (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)] :
    ∃(P : Sylow p (Projective CartanMatrix.E₆ K)) (g : Projective CartanMatrix.E₆ K),
      Subgroup.closure ((P : Set (Projective CartanMatrix.E₆ K)) ∪
        (P : Subgroup (Projective CartanMatrix.E₆ K)).map (MulAut.conj g).toMonoidHom)=⊤ :=
  original_two_conjugate_sylows_of_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_transpose
    E6_positive_definite E6Base E6Index E6_simple_sign
    CFSGNormTwoCoordinateHeight.coordinateHeight
    (CFSGNormTwoCoordinateHeight.simple_height CartanMatrix.E₆ CartanMatrix.E₆_diag
      CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos)
    K p E6_cartan 0

theorem serreTypeE7_two_conjugate_sylows (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)] :
    ∃(P : Sylow p (Projective CartanMatrix.E₇ K)) (g : Projective CartanMatrix.E₇ K),
      Subgroup.closure ((P : Set (Projective CartanMatrix.E₇ K)) ∪
        (P : Subgroup (Projective CartanMatrix.E₇ K)).map (MulAut.conj g).toMonoidHom)=⊤ :=
  original_two_conjugate_sylows_of_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_transpose
    E7_positive_definite E7Base E7Index E7_simple_sign
    CFSGNormTwoCoordinateHeight.coordinateHeight
    (CFSGNormTwoCoordinateHeight.simple_height CartanMatrix.E₇ CartanMatrix.E₇_diag
      CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos)
    K p E7_cartan 0

theorem serreTypeE8_two_conjugate_sylows (K : Type) [Field K] [Finite K]
    (p : ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)] :
    ∃(P : Sylow p (Projective CartanMatrix.E₈ K)) (g : Projective CartanMatrix.E₈ K),
      Subgroup.closure ((P : Set (Projective CartanMatrix.E₈ K)) ∪
        (P : Subgroup (Projective CartanMatrix.E₈ K)).map (MulAut.conj g).toMonoidHom)=⊤ :=
  original_two_conjugate_sylows_of_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_transpose
    E8_positive_definite E8Base E8Index E8_simple_sign
    CFSGNormTwoCoordinateHeight.coordinateHeight
    (CFSGNormTwoCoordinateHeight.simple_height CartanMatrix.E₈ CartanMatrix.E₈_diag
      CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos)
    K p E8_cartan 0

theorem typeE6_two_conjugate_sylows (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E6 q)] :
    ∃(P : Sylow q.prime (CFSG.Models.E6 q)) (g : CFSG.Models.E6 q),
      Subgroup.closure ((P : Set (CFSG.Models.E6 q)) ∪
        (P : Subgroup (CFSG.Models.E6 q)).map (MulAut.conj g).toMonoidHom)=⊤ := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE6_two_conjugate_sylows q.Field q.prime

theorem typeE7_two_conjugate_sylows (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E7 q)] :
    ∃(P : Sylow q.prime (CFSG.Models.E7 q)) (g : CFSG.Models.E7 q),
      Subgroup.closure ((P : Set (CFSG.Models.E7 q)) ∪
        (P : Subgroup (CFSG.Models.E7 q)).map (MulAut.conj g).toMonoidHom)=⊤ := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE7_two_conjugate_sylows q.Field q.prime

theorem typeE8_two_conjugate_sylows (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.E8 q)] :
    ∃(P : Sylow q.prime (CFSG.Models.E8 q)) (g : CFSG.Models.E8 q),
      Subgroup.closure ((P : Set (CFSG.Models.E8 q)) ∪
        (P : Subgroup (CFSG.Models.E8 q)).map (MulAut.conj g).toMonoidHom)=⊤ := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE8_two_conjugate_sylows q.Field q.prime

end SymmetricSubgroupAsymptotics.CFSGExceptionalGeckSylowGeneration
