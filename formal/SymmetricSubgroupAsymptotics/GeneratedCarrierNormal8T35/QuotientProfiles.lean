import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T35.Derived
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T35.RadicalProfiles
import SymmetricSubgroupAsymptotics.FiniteQuotientInvariantMasks

/-! Exact center and derived orders of all 28 original 8T35 quotients.
Selected by export_lean_carrier_profiles_selected.py. Stored carrier profiles
are not proof inputs; every mask is bound to the same original elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T35
local instance quotientProfilesSourceGroup : Group Source := BinaryMenuCayley8T35.group

def centerMask (i : Fin 28) (x : Fin 128) : Bool :=
  ((if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true] else (if i.val < 2 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,false,false,false,false,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,false,false,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,false,false,false,true,false,false,true])) else (if i.val < 5 then (if i.val < 4 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true]) else (if i.val < 6 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true]))) else (if i.val < 10 then (if i.val < 8 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true] else (if i.val < 9 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,true,true,false,false,false,false,true,true,true,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true])) else (if i.val < 12 then (if i.val < 11 then #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true] else #[false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,false,false,true,true,false,false,true,false,true,true,false,false,true,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,false,true,true,false,false,true,true,false,true,false,false,true,true,false,false,true]) else (if i.val < 13 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else (if i.val < 16 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) else (if i.val < 19 then (if i.val < 18 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) else (if i.val < 20 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]))) else (if i.val < 24 then (if i.val < 22 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else (if i.val < 23 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true])) else (if i.val < 26 then (if i.val < 25 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]) else (if i.val < 27 then #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] else #[true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true]))))) : Array Bool)[x.val]!

def intersectionMask (i : Fin 28) (x : Fin 128) : Bool :=
  normalMask i x && normalMask 12 x

def centerLog (i : Fin 28) : ℕ := (if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 1 else 2)) else (if i.val < 5 then (if i.val < 4 then 2 else 2) else (if i.val < 6 then 1 else 1))) else (if i.val < 10 then (if i.val < 8 then 1 else (if i.val < 9 then 1 else 2)) else (if i.val < 12 then (if i.val < 11 then 1 else 1) else (if i.val < 13 then 3 else 2)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then 2 else (if i.val < 16 then 2 else 2)) else (if i.val < 19 then (if i.val < 18 then 2 else 2) else (if i.val < 20 then 1 else 1))) else (if i.val < 24 then (if i.val < 22 then 1 else (if i.val < 23 then 1 else 2)) else (if i.val < 26 then (if i.val < 25 then 1 else 1) else (if i.val < 27 then 1 else 0)))))
def derivedLog (i : Fin 28) : ℕ := (if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 4 else (if i.val < 2 then 3 else 2)) else (if i.val < 5 then (if i.val < 4 then 1 else 1) else (if i.val < 6 then 1 else 1))) else (if i.val < 10 then (if i.val < 8 then 1 else (if i.val < 9 then 1 else 1)) else (if i.val < 12 then (if i.val < 11 then 1 else 1) else (if i.val < 13 then 0 else 0)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then 0 else (if i.val < 16 then 0 else 0)) else (if i.val < 19 then (if i.val < 18 then 0 else 0) else (if i.val < 20 then 0 else 0))) else (if i.val < 24 then (if i.val < 22 then 0 else (if i.val < 23 then 0 else 0)) else (if i.val < 26 then (if i.val < 25 then 0 else 0) else (if i.val < 27 then 0 else 0)))))
def intersectionOrder (i : Fin 28) : ℕ := (if i.val < 14 then (if i.val < 7 then (if i.val < 3 then (if i.val < 1 then 1 else (if i.val < 2 then 2 else 4)) else (if i.val < 5 then (if i.val < 4 then 8 else 8) else (if i.val < 6 then 8 else 8))) else (if i.val < 10 then (if i.val < 8 then 8 else (if i.val < 9 then 8 else 8)) else (if i.val < 12 then (if i.val < 11 then 8 else 8) else (if i.val < 13 then 16 else 16)))) else (if i.val < 21 then (if i.val < 17 then (if i.val < 15 then 16 else (if i.val < 16 then 16 else 16)) else (if i.val < 19 then (if i.val < 18 then 16 else 16) else (if i.val < 20 then 16 else 16))) else (if i.val < 24 then (if i.val < 22 then 16 else (if i.val < 23 then 16 else 16)) else (if i.val < 26 then (if i.val < 25 then 16 else 16) else (if i.val < 27 then 16 else 16)))))

private theorem centerMask_checked0 : ∀ x : Fin 128,
    centerMask 0 x = true ↔ ∀ j : Fin 3,
      normalMask 0 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card0 :
    Fintype.card {x : Fin 128 // centerMask 0 x = true} = 2 := by
  decide +kernel

private theorem intersectionMask_card0 :
    Fintype.card {x : Fin 128 // intersectionMask 0 x = true} = 1 := by
  decide +kernel

private theorem centerMask_checked1 : ∀ x : Fin 128,
    centerMask 1 x = true ↔ ∀ j : Fin 3,
      normalMask 1 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card1 :
    Fintype.card {x : Fin 128 // centerMask 1 x = true} = 4 := by
  decide +kernel

private theorem intersectionMask_card1 :
    Fintype.card {x : Fin 128 // intersectionMask 1 x = true} = 2 := by
  decide +kernel

private theorem centerMask_checked2 : ∀ x : Fin 128,
    centerMask 2 x = true ↔ ∀ j : Fin 3,
      normalMask 2 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card2 :
    Fintype.card {x : Fin 128 // centerMask 2 x = true} = 16 := by
  decide +kernel

private theorem intersectionMask_card2 :
    Fintype.card {x : Fin 128 // intersectionMask 2 x = true} = 4 := by
  decide +kernel

private theorem centerMask_checked3 : ∀ x : Fin 128,
    centerMask 3 x = true ↔ ∀ j : Fin 3,
      normalMask 3 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card3 :
    Fintype.card {x : Fin 128 // centerMask 3 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card3 :
    Fintype.card {x : Fin 128 // intersectionMask 3 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked4 : ∀ x : Fin 128,
    centerMask 4 x = true ↔ ∀ j : Fin 3,
      normalMask 4 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card4 :
    Fintype.card {x : Fin 128 // centerMask 4 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card4 :
    Fintype.card {x : Fin 128 // intersectionMask 4 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked5 : ∀ x : Fin 128,
    centerMask 5 x = true ↔ ∀ j : Fin 3,
      normalMask 5 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card5 :
    Fintype.card {x : Fin 128 // centerMask 5 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card5 :
    Fintype.card {x : Fin 128 // intersectionMask 5 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked6 : ∀ x : Fin 128,
    centerMask 6 x = true ↔ ∀ j : Fin 3,
      normalMask 6 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card6 :
    Fintype.card {x : Fin 128 // centerMask 6 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card6 :
    Fintype.card {x : Fin 128 // intersectionMask 6 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked7 : ∀ x : Fin 128,
    centerMask 7 x = true ↔ ∀ j : Fin 3,
      normalMask 7 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card7 :
    Fintype.card {x : Fin 128 // centerMask 7 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card7 :
    Fintype.card {x : Fin 128 // intersectionMask 7 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked8 : ∀ x : Fin 128,
    centerMask 8 x = true ↔ ∀ j : Fin 3,
      normalMask 8 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card8 :
    Fintype.card {x : Fin 128 // centerMask 8 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card8 :
    Fintype.card {x : Fin 128 // intersectionMask 8 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked9 : ∀ x : Fin 128,
    centerMask 9 x = true ↔ ∀ j : Fin 3,
      normalMask 9 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card9 :
    Fintype.card {x : Fin 128 // centerMask 9 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card9 :
    Fintype.card {x : Fin 128 // intersectionMask 9 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked10 : ∀ x : Fin 128,
    centerMask 10 x = true ↔ ∀ j : Fin 3,
      normalMask 10 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card10 :
    Fintype.card {x : Fin 128 // centerMask 10 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card10 :
    Fintype.card {x : Fin 128 // intersectionMask 10 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked11 : ∀ x : Fin 128,
    centerMask 11 x = true ↔ ∀ j : Fin 3,
      normalMask 11 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card11 :
    Fintype.card {x : Fin 128 // centerMask 11 x = true} = 32 := by
  decide +kernel

private theorem intersectionMask_card11 :
    Fintype.card {x : Fin 128 // intersectionMask 11 x = true} = 8 := by
  decide +kernel

private theorem centerMask_checked12 : ∀ x : Fin 128,
    centerMask 12 x = true ↔ ∀ j : Fin 3,
      normalMask 12 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card12 :
    Fintype.card {x : Fin 128 // centerMask 12 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card12 :
    Fintype.card {x : Fin 128 // intersectionMask 12 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked13 : ∀ x : Fin 128,
    centerMask 13 x = true ↔ ∀ j : Fin 3,
      normalMask 13 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card13 :
    Fintype.card {x : Fin 128 // centerMask 13 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card13 :
    Fintype.card {x : Fin 128 // intersectionMask 13 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked14 : ∀ x : Fin 128,
    centerMask 14 x = true ↔ ∀ j : Fin 3,
      normalMask 14 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card14 :
    Fintype.card {x : Fin 128 // centerMask 14 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card14 :
    Fintype.card {x : Fin 128 // intersectionMask 14 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked15 : ∀ x : Fin 128,
    centerMask 15 x = true ↔ ∀ j : Fin 3,
      normalMask 15 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card15 :
    Fintype.card {x : Fin 128 // centerMask 15 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card15 :
    Fintype.card {x : Fin 128 // intersectionMask 15 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked16 : ∀ x : Fin 128,
    centerMask 16 x = true ↔ ∀ j : Fin 3,
      normalMask 16 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card16 :
    Fintype.card {x : Fin 128 // centerMask 16 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card16 :
    Fintype.card {x : Fin 128 // intersectionMask 16 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked17 : ∀ x : Fin 128,
    centerMask 17 x = true ↔ ∀ j : Fin 3,
      normalMask 17 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card17 :
    Fintype.card {x : Fin 128 // centerMask 17 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card17 :
    Fintype.card {x : Fin 128 // intersectionMask 17 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked18 : ∀ x : Fin 128,
    centerMask 18 x = true ↔ ∀ j : Fin 3,
      normalMask 18 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card18 :
    Fintype.card {x : Fin 128 // centerMask 18 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card18 :
    Fintype.card {x : Fin 128 // intersectionMask 18 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked19 : ∀ x : Fin 128,
    centerMask 19 x = true ↔ ∀ j : Fin 3,
      normalMask 19 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card19 :
    Fintype.card {x : Fin 128 // centerMask 19 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card19 :
    Fintype.card {x : Fin 128 // intersectionMask 19 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked20 : ∀ x : Fin 128,
    centerMask 20 x = true ↔ ∀ j : Fin 3,
      normalMask 20 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card20 :
    Fintype.card {x : Fin 128 // centerMask 20 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card20 :
    Fintype.card {x : Fin 128 // intersectionMask 20 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked21 : ∀ x : Fin 128,
    centerMask 21 x = true ↔ ∀ j : Fin 3,
      normalMask 21 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card21 :
    Fintype.card {x : Fin 128 // centerMask 21 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card21 :
    Fintype.card {x : Fin 128 // intersectionMask 21 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked22 : ∀ x : Fin 128,
    centerMask 22 x = true ↔ ∀ j : Fin 3,
      normalMask 22 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card22 :
    Fintype.card {x : Fin 128 // centerMask 22 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card22 :
    Fintype.card {x : Fin 128 // intersectionMask 22 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked23 : ∀ x : Fin 128,
    centerMask 23 x = true ↔ ∀ j : Fin 3,
      normalMask 23 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card23 :
    Fintype.card {x : Fin 128 // centerMask 23 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card23 :
    Fintype.card {x : Fin 128 // intersectionMask 23 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked24 : ∀ x : Fin 128,
    centerMask 24 x = true ↔ ∀ j : Fin 3,
      normalMask 24 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card24 :
    Fintype.card {x : Fin 128 // centerMask 24 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card24 :
    Fintype.card {x : Fin 128 // intersectionMask 24 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked25 : ∀ x : Fin 128,
    centerMask 25 x = true ↔ ∀ j : Fin 3,
      normalMask 25 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card25 :
    Fintype.card {x : Fin 128 // centerMask 25 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card25 :
    Fintype.card {x : Fin 128 // intersectionMask 25 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked26 : ∀ x : Fin 128,
    centerMask 26 x = true ↔ ∀ j : Fin 3,
      normalMask 26 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card26 :
    Fintype.card {x : Fin 128 // centerMask 26 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card26 :
    Fintype.card {x : Fin 128 // intersectionMask 26 x = true} = 16 := by
  decide +kernel

private theorem centerMask_checked27 : ∀ x : Fin 128,
    centerMask 27 x = true ↔ ∀ j : Fin 3,
      normalMask 27 (⁅(⟨x⟩ : Source), generators j⁆).index = true :=
  (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))

private theorem centerMask_card27 :
    Fintype.card {x : Fin 128 // centerMask 27 x = true} = 128 := by
  decide +kernel

private theorem intersectionMask_card27 :
    Fintype.card {x : Fin 128 // intersectionMask 27 x = true} = 16 := by
  decide +kernel

theorem centerMask_test (i : Fin 28) (x : Fin 128) :
    centerMask i x = true ↔ ∀ j : Fin 3,
      ⁅(⟨x⟩ : Source), generators j⁆ ∈ (states i).kernel := by
  have h : centerMask i x = true ↔ ∀ j : Fin 3,
      normalMask i (⁅(⟨x⟩ : Source), generators j⁆).index = true := by
    fin_cases i
    · exact centerMask_checked0 x
    · exact centerMask_checked1 x
    · exact centerMask_checked2 x
    · exact centerMask_checked3 x
    · exact centerMask_checked4 x
    · exact centerMask_checked5 x
    · exact centerMask_checked6 x
    · exact centerMask_checked7 x
    · exact centerMask_checked8 x
    · exact centerMask_checked9 x
    · exact centerMask_checked10 x
    · exact centerMask_checked11 x
    · exact centerMask_checked12 x
    · exact centerMask_checked13 x
    · exact centerMask_checked14 x
    · exact centerMask_checked15 x
    · exact centerMask_checked16 x
    · exact centerMask_checked17 x
    · exact centerMask_checked18 x
    · exact centerMask_checked19 x
    · exact centerMask_checked20 x
    · exact centerMask_checked21 x
    · exact centerMask_checked22 x
    · exact centerMask_checked23 x
    · exact centerMask_checked24 x
    · exact centerMask_checked25 x
    · exact centerMask_checked26 x
    · exact centerMask_checked27 x
  exact h.trans (forall_congr' (fun j => normalMask_mem i _))

theorem intersectionMask_mem (i : Fin 28) (x : Fin 128) :
    intersectionMask i x = true ↔
      (⟨x⟩ : Source) ∈ (states i).kernel ⊓ commutator Source := by
  rw [source_derived_eq]
  change (normalMask i x && normalMask 12 x) = true ↔ _
  rw [Bool.and_eq_true]
  exact and_congr (normalMask_mem i ⟨x⟩) (normalMask_mem 12 ⟨x⟩)

theorem centerMask_card (i : Fin 28) :
    Nat.card {x : Fin 128 // centerMask i x = true} =
      2 ^ centerLog i * Nat.card (states i).kernel := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i
  · change Fintype.card {x : Fin 128 // centerMask 0 x = true} =
      2 ^ 1 * Nat.card N0.kernel
    rw [N0.kernel_card]
    exact centerMask_card0
  · change Fintype.card {x : Fin 128 // centerMask 1 x = true} =
      2 ^ 1 * Nat.card N1.kernel
    rw [N1.kernel_card]
    exact centerMask_card1
  · change Fintype.card {x : Fin 128 // centerMask 2 x = true} =
      2 ^ 2 * Nat.card N2.kernel
    rw [N2.kernel_card]
    exact centerMask_card2
  · change Fintype.card {x : Fin 128 // centerMask 3 x = true} =
      2 ^ 2 * Nat.card N3.kernel
    rw [N3.kernel_card]
    exact centerMask_card3
  · change Fintype.card {x : Fin 128 // centerMask 4 x = true} =
      2 ^ 2 * Nat.card N4.kernel
    rw [N4.kernel_card]
    exact centerMask_card4
  · change Fintype.card {x : Fin 128 // centerMask 5 x = true} =
      2 ^ 1 * Nat.card N5.kernel
    rw [N5.kernel_card]
    exact centerMask_card5
  · change Fintype.card {x : Fin 128 // centerMask 6 x = true} =
      2 ^ 1 * Nat.card N6.kernel
    rw [N6.kernel_card]
    exact centerMask_card6
  · change Fintype.card {x : Fin 128 // centerMask 7 x = true} =
      2 ^ 1 * Nat.card N7.kernel
    rw [N7.kernel_card]
    exact centerMask_card7
  · change Fintype.card {x : Fin 128 // centerMask 8 x = true} =
      2 ^ 1 * Nat.card N8.kernel
    rw [N8.kernel_card]
    exact centerMask_card8
  · change Fintype.card {x : Fin 128 // centerMask 9 x = true} =
      2 ^ 2 * Nat.card N9.kernel
    rw [N9.kernel_card]
    exact centerMask_card9
  · change Fintype.card {x : Fin 128 // centerMask 10 x = true} =
      2 ^ 1 * Nat.card N10.kernel
    rw [N10.kernel_card]
    exact centerMask_card10
  · change Fintype.card {x : Fin 128 // centerMask 11 x = true} =
      2 ^ 1 * Nat.card N11.kernel
    rw [N11.kernel_card]
    exact centerMask_card11
  · change Fintype.card {x : Fin 128 // centerMask 12 x = true} =
      2 ^ 3 * Nat.card N12.kernel
    rw [N12.kernel_card]
    exact centerMask_card12
  · change Fintype.card {x : Fin 128 // centerMask 13 x = true} =
      2 ^ 2 * Nat.card N13.kernel
    rw [N13.kernel_card]
    exact centerMask_card13
  · change Fintype.card {x : Fin 128 // centerMask 14 x = true} =
      2 ^ 2 * Nat.card N14.kernel
    rw [N14.kernel_card]
    exact centerMask_card14
  · change Fintype.card {x : Fin 128 // centerMask 15 x = true} =
      2 ^ 2 * Nat.card N15.kernel
    rw [N15.kernel_card]
    exact centerMask_card15
  · change Fintype.card {x : Fin 128 // centerMask 16 x = true} =
      2 ^ 2 * Nat.card N16.kernel
    rw [N16.kernel_card]
    exact centerMask_card16
  · change Fintype.card {x : Fin 128 // centerMask 17 x = true} =
      2 ^ 2 * Nat.card N17.kernel
    rw [N17.kernel_card]
    exact centerMask_card17
  · change Fintype.card {x : Fin 128 // centerMask 18 x = true} =
      2 ^ 2 * Nat.card N18.kernel
    rw [N18.kernel_card]
    exact centerMask_card18
  · change Fintype.card {x : Fin 128 // centerMask 19 x = true} =
      2 ^ 1 * Nat.card N19.kernel
    rw [N19.kernel_card]
    exact centerMask_card19
  · change Fintype.card {x : Fin 128 // centerMask 20 x = true} =
      2 ^ 1 * Nat.card N20.kernel
    rw [N20.kernel_card]
    exact centerMask_card20
  · change Fintype.card {x : Fin 128 // centerMask 21 x = true} =
      2 ^ 1 * Nat.card N21.kernel
    rw [N21.kernel_card]
    exact centerMask_card21
  · change Fintype.card {x : Fin 128 // centerMask 22 x = true} =
      2 ^ 1 * Nat.card N22.kernel
    rw [N22.kernel_card]
    exact centerMask_card22
  · change Fintype.card {x : Fin 128 // centerMask 23 x = true} =
      2 ^ 2 * Nat.card N23.kernel
    rw [N23.kernel_card]
    exact centerMask_card23
  · change Fintype.card {x : Fin 128 // centerMask 24 x = true} =
      2 ^ 1 * Nat.card N24.kernel
    rw [N24.kernel_card]
    exact centerMask_card24
  · change Fintype.card {x : Fin 128 // centerMask 25 x = true} =
      2 ^ 1 * Nat.card N25.kernel
    rw [N25.kernel_card]
    exact centerMask_card25
  · change Fintype.card {x : Fin 128 // centerMask 26 x = true} =
      2 ^ 1 * Nat.card N26.kernel
    rw [N26.kernel_card]
    exact centerMask_card26
  · change Fintype.card {x : Fin 128 // centerMask 27 x = true} =
      2 ^ 0 * Nat.card N27.kernel
    rw [N27.kernel_card]
    exact centerMask_card27

theorem intersectionMask_card (i : Fin 28) :
    Nat.card {x : Fin 128 // intersectionMask i x = true} = intersectionOrder i := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i
  · exact intersectionMask_card0
  · exact intersectionMask_card1
  · exact intersectionMask_card2
  · exact intersectionMask_card3
  · exact intersectionMask_card4
  · exact intersectionMask_card5
  · exact intersectionMask_card6
  · exact intersectionMask_card7
  · exact intersectionMask_card8
  · exact intersectionMask_card9
  · exact intersectionMask_card10
  · exact intersectionMask_card11
  · exact intersectionMask_card12
  · exact intersectionMask_card13
  · exact intersectionMask_card14
  · exact intersectionMask_card15
  · exact intersectionMask_card16
  · exact intersectionMask_card17
  · exact intersectionMask_card18
  · exact intersectionMask_card19
  · exact intersectionMask_card20
  · exact intersectionMask_card21
  · exact intersectionMask_card22
  · exact intersectionMask_card23
  · exact intersectionMask_card24
  · exact intersectionMask_card25
  · exact intersectionMask_card26
  · exact intersectionMask_card27

theorem source_intersection_card (i : Fin 28) :
    Nat.card ↥((states i).kernel ⊓ commutator Source) = intersectionOrder i := by
  let e := sourceIndexEquiv.subtypeEquiv (intersectionMask_mem i)
  exact (Nat.card_congr e).symm.trans (intersectionMask_card i)

theorem source_quotient_center_card (i : Fin 28) :
    Nat.card (Subgroup.center (Source ⧸ (states i).kernel)) = 2 ^ centerLog i :=
  quotientCenter_card_of_mask (states i).kernel generators generators_full sourceIndexEquiv
    (fun x => centerMask i x = true) (centerMask_test i) _ (centerMask_card i)

theorem source_quotient_derived_card (i : Fin 28) :
    Nat.card (commutator (Source ⧸ (states i).kernel)) = 2 ^ derivedLog i := by
  apply quotientCommutator_card_of_inf_card
  rw [source_derived_card, source_intersection_card]
  fin_cases i <;> decide +kernel

/-- The original tuple and all original elements are transported together. -/
def originalAmbientGenerators (j : Fin 3) : Original :=
  BinaryMenuCayley8T35.originalEquiv (generators j)

theorem originalAmbientGenerators_full :
    Subgroup.closure (Set.range originalAmbientGenerators) = ⊤ := by
  have h := congrArg (fun K : Subgroup Source =>
    K.map BinaryMenuCayley8T35.originalEquiv.toMonoidHom) generators_full
  dsimp only at h
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective
    BinaryMenuCayley8T35.originalEquiv.toMonoidHom
    BinaryMenuCayley8T35.originalEquiv.surjective] at h
  have hs : BinaryMenuCayley8T35.originalEquiv.toMonoidHom '' Set.range generators =
      Set.range originalAmbientGenerators := by
    ext x
    simp [originalAmbientGenerators]
  rwa [hs] at h

def originalIndexEquiv : Fin 128 ≃ Original :=
  sourceIndexEquiv.trans BinaryMenuCayley8T35.originalEquiv.toEquiv

theorem originalEquiv_mem_originalKernel (i : Fin 28) (x : Source) :
    BinaryMenuCayley8T35.originalEquiv x ∈ originalKernel i ↔ x ∈ (states i).kernel := by
  constructor
  · rintro ⟨y, hy, he⟩
    exact BinaryMenuCayley8T35.originalEquiv.injective he ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem original_derived_eq : commutator Original = originalKernel 12 := by
  have h : (commutator Source).map BinaryMenuCayley8T35.originalEquiv.toMonoidHom =
      commutator Original := by
    have hr : BinaryMenuCayley8T35.originalEquiv.toMonoidHom.range = ⊤ :=
      MonoidHom.range_eq_top.mpr BinaryMenuCayley8T35.originalEquiv.surjective
    rw [map_commutator_eq, hr, ← commutator_def]
  exact h.symm.trans (congrArg (fun K : Subgroup Source =>
    K.map BinaryMenuCayley8T35.originalEquiv.toMonoidHom) source_derived_eq)

theorem original_derived_card : Nat.card (commutator Original) = 16 := by
  rw [original_derived_eq]
  exact original_card 12

theorem original_centerMask_test (i : Fin 28) (x : Fin 128) :
    centerMask i x = true ↔ ∀ j : Fin 3,
      ⁅originalIndexEquiv x, originalAmbientGenerators j⁆ ∈ originalKernel i := by
  apply (centerMask_test i x).trans
  apply forall_congr'
  intro j
  have h := originalEquiv_mem_originalKernel i ⁅(⟨x⟩ : Source), generators j⁆
  simpa only [map_commutatorElement] using h.symm

theorem original_intersectionMask_mem (i : Fin 28) (x : Fin 128) :
    intersectionMask i x = true ↔
      originalIndexEquiv x ∈ originalKernel i ⊓ commutator Original := by
  rw [original_derived_eq]
  change (normalMask i x && normalMask 12 x) = true ↔ _
  rw [Bool.and_eq_true]
  exact and_congr ((normalMask_mem i ⟨x⟩).trans
    (originalEquiv_mem_originalKernel i ⟨x⟩).symm)
    ((normalMask_mem 12 ⟨x⟩).trans (originalEquiv_mem_originalKernel 12 ⟨x⟩).symm)

theorem original_intersection_card (i : Fin 28) :
    Nat.card ↥(originalKernel i ⊓ commutator Original) = intersectionOrder i := by
  let e := originalIndexEquiv.subtypeEquiv (original_intersectionMask_mem i)
  exact (Nat.card_congr e).symm.trans (intersectionMask_card i)

theorem original_quotient_center_card (i : Fin 28) :
    Nat.card (Subgroup.center (Original ⧸ originalKernel i)) = 2 ^ centerLog i := by
  apply quotientCenter_card_of_mask (originalKernel i) originalAmbientGenerators
    originalAmbientGenerators_full originalIndexEquiv (fun x => centerMask i x = true)
    (original_centerMask_test i)
  have h := centerMask_card i
  rw [state_card] at h
  simpa only [original_card] using h

theorem original_quotient_derived_card (i : Fin 28) :
    Nat.card (commutator (Original ⧸ originalKernel i)) = 2 ^ derivedLog i := by
  apply quotientCommutator_card_of_inf_card
  rw [original_derived_card, original_intersection_card]
  fin_cases i <;> decide +kernel

/-- Every actual original normal has the certified quotient fields c,g.
The independent head-maximum and physical-weight tasks are not assumed. -/
theorem complete_original_quotient_profiles (N : Subgroup Original) [N.Normal] :
    ∃ i : Fin 28, originalKernel i = N ∧
      Nat.card (Subgroup.center (Original ⧸ N)) = 2 ^ centerLog i ∧
      Nat.card (commutator (Original ⧸ N)) = 2 ^ derivedLog i := by
  obtain ⟨i, hi⟩ := complete_original N
  change originalKernel i = N at hi
  subst N
  exact ⟨i, rfl, original_quotient_center_card i, original_quotient_derived_card i⟩

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T35
