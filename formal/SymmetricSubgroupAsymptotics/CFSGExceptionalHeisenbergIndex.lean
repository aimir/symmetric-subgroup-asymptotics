import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergOriginal
import SymmetricSubgroupAsymptotics.CFSGExceptionalHeisenbergPadding
import SymmetricSubgroupAsymptotics.CFSGExceptionalGeckIntegralData

/-! Every proper subgroup of the SAME original E6/E7/E8 projective
model has index at least p^11, hence at least 2048. The prime-field
Heisenberg subgroup and its literal centre are constructed, not assumed.
All fields and all characteristics, including two, are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReduction
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalHeisenbergRootPilot
local instance heisenbergE6RootsDecidableEq : DecidableEq (Roots CartanMatrix.E₆) := Classical.decEq _
local instance heisenbergE7RootsDecidableEq : DecidableEq (Roots CartanMatrix.E₇) := Classical.decEq _
local instance heisenbergE8RootsDecidableEq : DecidableEq (Roots CartanMatrix.E₈) := Classical.decEq _

private theorem heisenberg_index_of_coordinate_cartan_eq {r:ℕ}
    (A:Matrix (Fin r) (Fin r) ℤ)(hd:∀i,A i i=2)(hs:A.transpose=A)
    (hp:(rationalMatrix A).PosDef)(ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)][DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced][(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)](K:Type)[Field K][Finite K](C:RootConfig A 10)
    {B:Matrix (Fin r) (Fin r) ℤ}
    (hB:cartan (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho)=B)
    (p:ℕ)[Fact p.Prime][CharP K p][IsSimpleGroup (Projective B K)]
    (H:Subgroup (Projective B K))(hH:H≠⊤) : p^11≤H.index := by
  subst B
  exact CFSGExceptionalHeisenbergOriginal.prime_power_le_proper_index A hd hs hp ho C K p
    (Classical.arbitrary (Fin r)) H hH

theorem serreTypeE6_prime_eleventh_le_index (K:Type)[Field K][Finite K]
    (p:ℕ)[Fact p.Prime][CharP K p][IsSimpleGroup (Projective CartanMatrix.E₆ K)]
    (H:Subgroup (Projective CartanMatrix.E₆ K))(hH:H≠⊤) : p^11≤H.index := by
  exact heisenberg_index_of_coordinate_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K CFSGExceptionalHeisenbergRootPilot.E6
    (B:=CartanMatrix.E₆) (by
      ext i j
      exact coordinate_cartan_transpose CartanMatrix.E₆ CartanMatrix.E₆_diag
        CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos i j) p H hH

theorem typeE6_prime_eleventh_le_index (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E6 q)](H:Subgroup (CFSG.Models.E6 q))(hH:H≠⊤) :
    q.prime^11≤H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE6_prime_eleventh_le_index q.Field q.prime H hH

theorem typeE6_2048_le_index (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E6 q)](H:Subgroup (CFSG.Models.E6 q))(hH:H≠⊤) :
    2048≤H.index := by
  calc
    2048=2^11 := by norm_num
    _≤q.prime^11 := Nat.pow_le_pow_left q.prime_isPrime.two_le 11
    _≤H.index := typeE6_prime_eleventh_le_index q H hH

theorem serreTypeE7_prime_eleventh_le_index (K:Type)[Field K][Finite K]
    (p:ℕ)[Fact p.Prime][CharP K p][IsSimpleGroup (Projective CartanMatrix.E₇ K)]
    (H:Subgroup (Projective CartanMatrix.E₇ K))(hH:H≠⊤) : p^11≤H.index := by
  exact heisenberg_index_of_coordinate_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos K CFSGExceptionalHeisenbergPadding.E7
    (B:=CartanMatrix.E₇) (by
      ext i j
      exact coordinate_cartan_transpose CartanMatrix.E₇ CartanMatrix.E₇_diag
        CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos i j) p H hH

theorem typeE7_prime_eleventh_le_index (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E7 q)](H:Subgroup (CFSG.Models.E7 q))(hH:H≠⊤) :
    q.prime^11≤H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE7_prime_eleventh_le_index q.Field q.prime H hH

theorem typeE7_2048_le_index (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E7 q)](H:Subgroup (CFSG.Models.E7 q))(hH:H≠⊤) :
    2048≤H.index := by
  calc
    2048=2^11 := by norm_num
    _≤q.prime^11 := Nat.pow_le_pow_left q.prime_isPrime.two_le 11
    _≤H.index := typeE7_prime_eleventh_le_index q H hH

theorem serreTypeE8_prime_eleventh_le_index (K:Type)[Field K][Finite K]
    (p:ℕ)[Fact p.Prime][CharP K p][IsSimpleGroup (Projective CartanMatrix.E₈ K)]
    (H:Subgroup (Projective CartanMatrix.E₈ K))(hH:H≠⊤) : p^11≤H.index := by
  exact heisenberg_index_of_coordinate_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos K CFSGExceptionalHeisenbergPadding.E8
    (B:=CartanMatrix.E₈) (by
      ext i j
      exact coordinate_cartan_transpose CartanMatrix.E₈ CartanMatrix.E₈_diag
        CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos i j) p H hH

theorem typeE8_prime_eleventh_le_index (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E8 q)](H:Subgroup (CFSG.Models.E8 q))(hH:H≠⊤) :
    q.prime^11≤H.index := by
  letI : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
  exact serreTypeE8_prime_eleventh_le_index q.Field q.prime H hH

theorem typeE8_2048_le_index (q:CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.E8 q)](H:Subgroup (CFSG.Models.E8 q))(hH:H≠⊤) :
    2048≤H.index := by
  calc
    2048=2^11 := by norm_num
    _≤q.prime^11 := Nat.pow_le_pow_left q.prime_isPrime.two_le 11
    _≤H.index := typeE8_prime_eleventh_le_index q H hH

end SymmetricSubgroupAsymptotics.CFSGReduction
