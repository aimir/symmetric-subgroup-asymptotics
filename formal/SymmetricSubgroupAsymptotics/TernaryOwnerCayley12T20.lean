import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Literal c=1 high action certificate 12T20

Generated from certificates/data/primitive_rank.jsonl.gz by export_lean_c1_degree_twelve.py.
Selected transitive row 194; raw-line SHA256 dde71043dc48e6365a3de190c501751a0587eb3e5ccbe7b84f9e8b6038f41054.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This proves the literal selected action only;
high-pair coverage and earlier-owner acceptance remain separate theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerCayley12T20

private def generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[0,7,5,6,4,11,9,10,8,3,1,2] : Array (Fin 12))[x.val]!
  invFun x := (#[0,10,11,9,4,2,3,1,8,6,7,5] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6,4,5,3,10,8,9,7,2,0,1,11] : Array (Fin 12))[x.val]!
  invFun x := (#[9,10,8,3,1,2,0,7,5,6,4,11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4,5,6,7,8,9,10,11,0,1,2,3] : Array (Fin 12))[x.val]!
  invFun x := (#[8,9,10,11,0,1,2,3,4,5,6,7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 12) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 36) : Fin (12^12) :=
  Fin.ofNat 8916100448256 (((if (i.val) / 32 < 1 then 3083313688393876925445102468969022136391327741354646410026206796159981253277667758735534306581155393406415129030448206733983070555141428518582725944584246194270056617300380858877635308444384632351186560400303777934509315513844320694276097398677838529331804572909884337457664679800353345882021738454296950695661627749264456372219875190033027801276552867763945864357094609439040573957008013386098774967148669736237332393605093 else 48142679234183262435127982672565280978990454406574652) : ℕ) / 2 ^ (44 * ((i.val) % 32)) % 2 ^ 44)
private def ranks (i : Fin 36) : ℕ :=
  (((if (i.val) / 32 < 1 then 2501326550495851419021447099331458466254261287846587246556 else 32911) : ℕ) / 2 ^ (6 * ((i.val) % 32)) % 2 ^ 6)
private def parents (i : Fin 36) : Fin 36 :=
  Fin.ofNat 36 (((if (i.val) / 32 < 1 then 1991100546145664122764490381879165167859801657781899073050 else 9312466) : ℕ) / 2 ^ (6 * ((i.val) % 32)) % 2 ^ 6)
private def letters (i : Fin 36) : Fin 3 :=
  Fin.ofNat 3 (((if (i.val) / 32 < 1 then 12286007405533809322 else 22) : ℕ) / 2 ^ (2 * ((i.val) % 32)) % 2 ^ 2)
private def nextRow (i : Fin 36) (j : Fin 3) : Fin 36 :=
  Fin.ofNat 36 (((if (i.val * 3 + j.val) / 32 < 2 then (if (i.val * 3 + j.val) / 32 < 1 then 1122317379765945409665801601782218364666794277542415880340 else 1323002903996101191776263260670391986923884827810001621015) else (if (i.val * 3 + j.val) / 32 < 3 then 831118240616930254746865892757430855010875209685279836310 else 702240534651016603588)) : ℕ) / 2 ^ (6 * ((i.val * 3 + j.val) % 32)) % 2 ^ 6)
private def prevRow (i : Fin 36) (j : Fin 3) : Fin 36 :=
  Fin.ofNat 36 (((if (i.val * 3 + j.val) / 32 < 2 then (if (i.val * 3 + j.val) / 32 < 1 then 886624794083008673687264447526264418147453448005209661515 else 3053162174563318191175915113258713419260257713458455815457) else (if (i.val * 3 + j.val) / 32 < 3 then 2010952728223137574061938614117138748887837069795422126807 else 1662807096704316549014)) : ℕ) / 2 ^ (6 * ((i.val * 3 + j.val) % 32)) % 2 ^ 6)

private theorem parent_lt_checked : ∀ i : Fin 36,
    i ≠ 35 → ranks (parents i) < ranks i := (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))
private theorem parent_next_checked : ∀ i : Fin 36,
    i ≠ 35 → nextRow (parents i) (letters i) = i := (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 36 where
  rows := codes
  identity := 35
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (Fin.addCases (m := 17) (n := 18) (Fin.addCases (m := 8) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 36 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 36) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 36 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

/-- Exact one-based image lists bind the selected original source tuple. -/
theorem sourceGenerator_images : ∀ j : Fin 3, ∀ x : Fin 12,
    (generators j x).val + 1 =
      ((#[#[1,8,6,7,5,12,10,11,9,4,2,3],#[7,5,6,4,11,9,10,8,3,1,2,12],#[5,6,7,8,9,10,11,12,1,2,3,4]] : Array (Array ℕ))[j.val]!)[x.val]! := by
  decide +kernel

end SymmetricSubgroupAsymptotics.TernaryOwnerCayley12T20
