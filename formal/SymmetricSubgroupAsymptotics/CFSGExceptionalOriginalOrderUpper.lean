import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateOriginalOrderUpper
import SymmetricSubgroupAsymptotics.CFSGE6FiniteRootMenu
import SymmetricSubgroupAsymptotics.CFSGE7FiniteRootMenu
import SymmetricSubgroupAsymptotics.CFSGE8FiniteRootMenu
import SymmetricSubgroupAsymptotics.CFSGExceptionalCartanNeighbors

/-! Upper orders of the actual original E6/E7/E8 projective models.
Finite reflection menus bound positive roots and word values; the
actual positive and torus images give the other Bruhat factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalOrderUpper
open CFSG.Models.Chevalley CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGGeckSerreRepresentation CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGExceptionalCartanPositiveDefinite CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanNeighbors CFSGNormTwoCoordinateOriginalOrderUpper
local instance : DecidableEq (Roots CartanMatrix.E₆):=Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₇):=Classical.decEq _
local instance : DecidableEq (Roots CartanMatrix.E₈):=Classical.decEq _

private theorem order_bound_of_cartan_eq {r:ℕ}
    (A:Matrix (Fin r) (Fin r) ℤ) (hd:∀i,A i i=2)
    (hs:A.transpose=A) (hp:(rationalMatrix A).PosDef) (ho:∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
    [Nontrivial (Fin r)] (K:Type) [Field K] [Finite K]
    {C:Matrix (Fin r) (Fin r) ℤ}
    (hC:cartan (coordinateBase A hd hs hp ho) (coordinateIndexEquiv A hd hs hp ho)=C)
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective C K)]
    (hneighbors:∀j,∃k,A j k= -1) (hn:¬IsMulCommutative (Projective C K))
    (u c s:ℕ) (hpos:Nat.card (PositiveRoot A)≤u) (hroot:Nat.card (Roots A)≤c)
    (hmenu:2*c≤Nat.card K^s) : Nat.card (Projective C K)≤Nat.card K^(2*u+r+s*r) := by
  subst C
  exact original_order_le_power A hd hs hp ho K p (Classical.arbitrary _) hneighbors hn
    u c s hpos hroot hmenu

theorem serreTypeE6_order_le (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₆ K)]
    (hn:¬IsMulCommutative (Projective CartanMatrix.E₆ K)) :
    Nat.card (Projective CartanMatrix.E₆ K)≤Nat.card K^126 := by
  exact order_bound_of_cartan_eq CartanMatrix.E₆ CartanMatrix.E₆_diag
    CartanMatrix.E₆_transpose E6_positive_definite CartanMatrix.E₆_off_diag_nonpos K E6_cartan p
    E6_neighbor hn 36 72 8 CFSGE6FiniteRootMenu.positive_roots_card_le CFSGE6FiniteRootMenu.roots_card_le
    ((by decide:2*72≤2^8).trans (Nat.pow_le_pow_left Finite.one_lt_card 8))

theorem serreTypeE7_order_le (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₇ K)]
    (hn:¬IsMulCommutative (Projective CartanMatrix.E₇ K)) :
    Nat.card (Projective CartanMatrix.E₇ K)≤Nat.card K^189 := by
  exact order_bound_of_cartan_eq CartanMatrix.E₇ CartanMatrix.E₇_diag
    CartanMatrix.E₇_transpose E7_positive_definite CartanMatrix.E₇_off_diag_nonpos K E7_cartan p
    E7_neighbor hn 63 126 8 CFSGE7FiniteRootMenu.positive_roots_card_le CFSGE7FiniteRootMenu.roots_card_le
    ((by decide:2*126≤2^8).trans (Nat.pow_le_pow_left Finite.one_lt_card 8))

theorem serreTypeE8_order_le (K:Type) [Field K] [Finite K]
    (p:ℕ) [Fact p.Prime] [CharP K p] [IsSimpleGroup (Projective CartanMatrix.E₈ K)]
    (hn:¬IsMulCommutative (Projective CartanMatrix.E₈ K)) :
    Nat.card (Projective CartanMatrix.E₈ K)≤Nat.card K^320 := by
  exact order_bound_of_cartan_eq CartanMatrix.E₈ CartanMatrix.E₈_diag
    CartanMatrix.E₈_transpose E8_positive_definite CartanMatrix.E₈_off_diag_nonpos K E8_cartan p
    E8_neighbor hn 120 240 9 CFSGE8FiniteRootMenu.positive_roots_card_le CFSGE8FiniteRootMenu.roots_card_le
    ((by decide:2*240≤2^9).trans (Nat.pow_le_pow_left Finite.one_lt_card 9))

end SymmetricSubgroupAsymptotics.CFSGExceptionalOriginalOrderUpper
