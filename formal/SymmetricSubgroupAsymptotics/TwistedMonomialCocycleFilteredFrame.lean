import SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFrame

/-! Keep a genuine predicate on the actual root restriction while using
the twisted frame encoding. In particular, an onto-local-hom predicate
must restrict BOTH the source cocycles and the target root cocycles. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFilteredFrame
open TwistedMonomialCocycleFrame

variable {Q X A : Type*} [Group Q] [Group A] [MulAction Q X]
variable (rho : Q →* MulAut (X → A)) (theta : Q → X → MulAut A)
variable (hcoord : ∀ q : Q, ∀ f : X → A, ∀ x : X,
  (rho q f) (q • x)=theta q x (f x))

def encode (x0 : X) (t : X → Q)
    (P : Cocycle (rootAction rho theta hcoord x0) → Prop)
    (c : {c : Cocycle rho // P (rootRestriction rho theta hcoord x0 c)}) :
    (X → A) × {r : Cocycle (rootAction rho theta hcoord x0) // P r} :=
  (frame rho t c.val,⟨rootRestriction rho theta hcoord x0 c.val,c.property⟩)

theorem encode_injective (x0 : X) (t : X → Q) (ht : ∀ x : X, t x • x0=x)
    (P : Cocycle (rootAction rho theta hcoord x0) → Prop) :
    Function.Injective (encode rho theta hcoord x0 t P) := by
  intro c d he
  apply Subtype.ext
  apply TwistedMonomialCocycleFrame.encode_injective rho theta hcoord x0 t ht
  exact congrArg
    (fun z : (X → A) × {r : Cocycle (rootAction rho theta hcoord x0) // P r} =>
      (z.1,z.2.val)) he

theorem card_le_frame_filtered_root [Finite X] [Finite A] (x0 : X)
    (P : Cocycle (rootAction rho theta hcoord x0) → Prop)
    [Finite {r : Cocycle (rootAction rho theta hcoord x0) // P r}]
    (t : X → Q) (ht : ∀ x : X, t x • x0=x) :
    Nat.card {c : Cocycle rho // P (rootRestriction rho theta hcoord x0 c)} ≤
      Nat.card A ^ Nat.card X *
        Nat.card {r : Cocycle (rootAction rho theta hcoord x0) // P r} := by
  have h := Nat.card_le_card_of_injective (encode rho theta hcoord x0 t P)
    (encode_injective rho theta hcoord x0 t ht P)
  simpa only [Nat.card_prod,Nat.card_fun] using h

theorem card_le_transitive_filtered [Finite Q] [Finite X] [Finite A]
    [MulAction.IsPretransitive Q X] (x0 : X)
    (P : Cocycle (rootAction rho theta hcoord x0) → Prop) :
    Nat.card {c : Cocycle rho // P (rootRestriction rho theta hcoord x0 c)} ≤
      Nat.card A ^ Nat.card X *
        Nat.card {r : Cocycle (rootAction rho theta hcoord x0) // P r} :=
  card_le_frame_filtered_root rho theta hcoord x0 P
    (transversal (Q := Q) x0) (transversal_spec (Q := Q) x0)

end SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFilteredFrame
