import SymmetricSubgroupAsymptotics.DiagonalInvariantSubmodules

/-! The exact invariant-submodule correspondence restricted to full
original coordinate projections. Each parameter is one subspace on one
distinct scalar isotype, retaining every correlation inside that isotype. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.DiagonalFullSubmoduleEquiv

open DiagonalInvariantSubmodules

variable {k ι J : Type*} [Field k] [Fintype ι] (scalar : ι → J → k)

def FullSubmodule (I : Type*) := {K : Submodule k (I → k) // FullCoordinates K}

def FullStable := {K : Stable scalar // FullCoordinates K.1}

/-- Restrict and reconstruct the same full-coordinate invariant space;
there is no extra choice of labelling or basis in either direction. -/
def equiv : FullStable scalar ≃ (∀ a : Label scalar, FullSubmodule (k := k) (Coordinate scalar a)) where
  toFun K a := ⟨encode scalar K.1 a,(fullCoordinates_iff scalar K.1).mp K.2 a⟩
  invFun L := ⟨decode scalar (fun a => (L a).1),by
    apply (fullCoordinates_iff scalar (decode scalar (fun a => (L a).1))).mpr
    rw [encode_decode]
    exact fun a => (L a).2⟩
  left_inv K := by
    apply Subtype.ext
    exact decode_encode scalar K.1
  right_inv L := by
    funext a
    apply Subtype.ext
    exact congrFun (encode_decode scalar (fun a => (L a).1)) a

@[simp] theorem equiv_apply_val (K : FullStable scalar) (a : Label scalar) :
    (equiv scalar K a).1=encode scalar K.1 a := rfl

@[simp] theorem equiv_symm_val
    (L : ∀ a : Label scalar, FullSubmodule (k := k) (Coordinate scalar a)) :
    ((equiv scalar).symm L).1=decode scalar (fun a => (L a).1) := rfl

end SymmetricSubgroupAsymptotics.DiagonalFullSubmoduleEquiv

end

