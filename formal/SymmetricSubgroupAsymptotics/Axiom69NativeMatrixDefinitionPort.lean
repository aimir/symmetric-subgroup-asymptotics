import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixData

/-! Definition-only port of CFSG/Blueprint/NativeSporadic.lean at
69cb972f587a3ecc035e092253167ff2e303c962 (Apache-2.0). The decoder and
seedMonoid bodies below retain the original formulas. Only imports,
visibility attributes and namespace packaging differ. This module imports
NO upstream classification, recognition, order, or4.35 proof object. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Axiom69NativeMatrixDefinitionPort

def asciiWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12

def decode (p d mode : ℕ) (s : String) : Matrix (Fin d) (Fin d) (ZMod p) :=
  let body := (s.toList.dropWhile (· != '\n')).drop 1
  let entries : List ℕ := if mode = 1 then
    (body.filter fun c => !asciiWhitespace c).map fun c =>
      if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0
    else
      ((String.ofList (body.map fun c => if asciiWhitespace c then ' ' else c)).splitOn " ").filter
        (· != "") |>.map fun token => if token.toList.all (fun c => '0' ≤ c && c ≤ '9') then token.toNat?.getD 0 else 0
  fun i j => (entries[i.val * d + j.val]?.getD 0 : ZMod p)

def seedMonoid (p d mode : ℕ) (s₁ s₂ : String) :
    Submonoid (Matrix (Fin d) (Fin d) (ZMod p)) :=
  Submonoid.closure {decode p d mode s₁, decode p d mode s₂}

end SymmetricSubgroupAsymptotics.Axiom69NativeMatrixDefinitionPort
