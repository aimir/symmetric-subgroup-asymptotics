import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-! Sixteen-bit codes for actual binary four-by-four matrices. Only sparse
selected-generator transitions are certified; there is no ambient product
table. Singular codes are allowed as codes, never asserted invertible. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.GeneralFourTwoMatrixEncoding

abbrev Ambient := Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)
abbrev Mat := Matrix (Fin 4) (Fin 4) (ZMod 2)

def encode (A : Mat) : Fin 65536 :=
  finFunctionFinEquiv (fun i : Fin 4 =>
    finFunctionFinEquiv (fun j : Fin 4 => (ZMod.finEquiv 2).symm (A i j)))

def decode (c : Fin 65536) : Mat :=
  fun i j => ZMod.finEquiv 2
    (finFunctionFinEquiv.symm ((finFunctionFinEquiv.symm c) i) j)

@[simp] theorem decode_encode (A : Mat) : decode (encode A) = A := by
  ext i j
  simp [decode, encode]

theorem encode_injective : Function.Injective encode := by
  intro A B h
  simpa only [decode_encode] using congrArg decode h

def encoding {ι : Type} (generators : ι → Ambient) :
    GeneratorEncoding generators (Fin 65536) where
  encode g := encode g.val
  injective := fun _ _ h => Units.ext (encode_injective h)
  one := encode 1
  encode_one := rfl
  step c j := encode (decode c * (generators j).val)
  encode_step g j := by
    change encode (g.val * (generators j).val) =
      encode (decode (encode g.val) * (generators j).val)
    rw [decode_encode]

theorem ambient_card : Nat.card Ambient = 20160 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h := Matrix.card_GL_field (𝔽 := ZMod 2) 4
  norm_num [Fin.prod_univ_succ] at h
  simpa only [Ambient, Nat.card_eq_fintype_card] using h

end SymmetricSubgroupAsymptotics.GeneralFourTwoMatrixEncoding
