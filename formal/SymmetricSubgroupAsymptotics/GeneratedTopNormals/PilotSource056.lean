import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Compact literal action certificate Top056

Generated from actual projected menu permutations by export_lean_top_registry.py.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This certifies
this original action, not finite-menu or normal-registry completeness.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryTopSource056

private def generator0 : Equiv.Perm (Fin 8) where
  toFun x := (#[0,1,2,3,6,7,4,5] : Array (Fin 8))[x.val]!
  invFun x := (#[0,1,2,3,6,7,4,5] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 8) where
  toFun x := (#[7,4,5,6,2,1,0,3] : Array (Fin 8))[x.val]!
  invFun x := (#[6,5,4,7,1,2,3,0] : Array (Fin 8))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 2) : Equiv.Perm (Fin 8) :=
  (if j.val < 1 then generator0 else generator1)

private def codes (i : Fin 16) : Fin (8^8) :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 859068 else 859950) else (if i.val < 3 then 2722293 else 2723175)) else (if i.val < 6 then (if i.val < 5 then 4471740 else 4472622) else (if i.val < 7 then 6334965 else 6335847))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 9924691 else 9925825) else (if i.val < 11 then 11788826 else 11789960)) else (if i.val < 14 then (if i.val < 13 then 14569555 else 14570689) else (if i.val < 15 then 16433690 else 16434824))))
private def ranks (i : Fin 16) : ℕ :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 11 else 9) else (if i.val < 3 then 6 else 4)) else (if i.val < 6 then (if i.val < 5 then 13 else 12) else (if i.val < 7 then 3 else 2))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 7 else 10) else (if i.val < 11 then 15 else 1)) else (if i.val < 14 then (if i.val < 13 then 5 else 8) else (if i.val < 15 then 14 else 0))))
private def parents (i : Fin 16) : Fin 16 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 8 else 12) else (if i.val < 3 then 6 else 7)) else (if i.val < 6 then (if i.val < 5 then 9 else 13) else (if i.val < 7 then 11 else 15))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 6 else 2) else (if i.val < 11 then 4 else 15)) else (if i.val < 14 then (if i.val < 13 then 7 else 3) else (if i.val < 15 then 5 else 15))))
private def letters (i : Fin 16) : Fin 2 :=
  (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 1 else 1) else (if i.val < 3 then 0 else 0)) else (if i.val < 6 then (if i.val < 5 then 1 else 1) else (if i.val < 7 then 1 else 1))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 1 else 1) else (if i.val < 11 then 1 else 0)) else (if i.val < 14 then (if i.val < 13 then 1 else 1) else (if i.val < 15 then 1 else 0))))
private def nextRow (i : Fin 16) (j : Fin 2) : Fin 16 :=
  ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,11] else #[5,15]) else (if i.val < 3 then #[6,9] else #[7,13])) else (if i.val < 6 then (if i.val < 5 then #[0,10] else #[1,14]) else (if i.val < 7 then #[2,8] else #[3,12]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,0] else #[13,4]) else (if i.val < 11 then #[14,2] else #[15,6])) else (if i.val < 14 then (if i.val < 13 then #[8,1] else #[9,5]) else (if i.val < 15 then #[10,3] else #[11,7])))) : Array (Fin 16))[j.val]!
def prevRow (i : Fin 16) (j : Fin 2) : Fin 16 :=
  ((if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then #[4,8] else #[5,12]) else (if i.val < 3 then #[6,10] else #[7,14])) else (if i.val < 6 then (if i.val < 5 then #[0,9] else #[1,13]) else (if i.val < 7 then #[2,11] else #[3,15]))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then #[12,6] else #[13,2]) else (if i.val < 11 then #[14,4] else #[15,0])) else (if i.val < 14 then (if i.val < 13 then #[8,7] else #[9,3]) else (if i.val < 15 then #[10,5] else #[11,1])))) : Array (Fin 16))[j.val]!

private theorem parent_lt_checked : ∀ i : Fin 16,
    i ≠ 15 → ranks (parents i) < ranks i := (by decide +kernel)
private theorem parent_next_checked : ∀ i : Fin 16,
    i ≠ 15 → nextRow (parents i) (letters i) = i := (by decide +kernel)

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 16 where
  rows := codes
  identity := 15
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (by decide +kernel)
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (by decide +kernel)

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 16 :=
  certificate.card_closure rows_injective

theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (by decide +kernel)

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 16) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 16 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

end SymmetricSubgroupAsymptotics.BinaryTopSource056
