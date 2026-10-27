import SymmetricSubgroupAsymptotics.SignedPermutationWordPointEncoding
import SymmetricSubgroupAsymptotics.FixedProductRelatorTransport

/-! A literal signed word in x,y is evaluated after y=h^-1*A. The raw
letter maps retain an arbitrary typed shadow, so packed Nat point maps
need only their actual forward/inverse bindings. No capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.FixedProductSignedWordPointEncoding
open SignedPermutationWordPointEvaluation SignedPermutationWordPointEncoding
open SignedPermutationWordPointEvaluation.Letter FixedProductRelatorTransport

def asFreeWord (w : List Letter) : FreeGroup (Fin 2) :=
  eval (FreeGroup.of 0) (FreeGroup.of 1) w

private theorem eval_map {G H : Type*} [Group G] [Group H]
    (phi : G →* H) (x y : G) (w : List Letter) :
    phi (eval x y w) = eval (phi x) (phi y) w := by
  induction w with
  | nil => exact map_one phi
  | cons s w ih =>
    cases s <;> simp only [eval,value,map_mul,map_inv,ih]

theorem lift_asFreeWord {G : Type*} [Group G] (x y : G) (w : List Letter) :
    FreeGroup.lift (pair x y) (asFreeWord w) = eval x y w := by
  simpa only [asFreeWord,FreeGroup.lift_apply_of,pair_zero,pair_one] using
    eval_map (FreeGroup.lift (pair x y)) (FreeGroup.of 0) (FreeGroup.of 1) w

def replacement : Letter → List Letter
  | first => [first]
  | firstInv => [firstInv]
  | second => [firstInv,second]
  | secondInv => [secondInv,first]

def fixedProductWord (w : List Letter) : List Letter := w.flatMap replacement

theorem eval_fixedProductWord {G : Type*} [Group G] (h A : G) (w : List Letter) :
    eval h A (fixedProductWord w) = eval h (h⁻¹*A) w := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    change eval h A (replacement s ++ fixedProductWord w) = _
    rw [eval_append,ih]
    cases s <;> simp only [replacement,eval,value,mul_one,mul_inv_rev,inv_inv]

theorem raw_word_eq {X Y : Type*} (encode : X → Y)
    (h A : Equiv.Perm X) (hf hi af ai : Y → Y)
    (hhf : ∀ p, hf (encode p) = encode (h p))
    (hhi : ∀ p, hi (encode p) = encode (h.symm p))
    (haf : ∀ p, af (encode p) = encode (A p))
    (hai : ∀ p, ai (encode p) = encode (A.symm p))
    (w : List Letter) (p : X) :
    applyWord hf hi af ai (fixedProductWord w) (encode p) =
      encode ((FreeGroup.lift (pair h (h⁻¹*A)) (asFreeWord w)) p) := by
  calc
    _ = encode (applyWord h h.symm A A.symm (fixedProductWord w) p) :=
      applyWord_encoding encode h h.symm A A.symm hf hi af ai hhf hhi haf hai _ p
    _ = _ := by
      have he : eval (G := Equiv.Perm X) h (h⁻¹*A) w =
          FreeGroup.lift (pair h (h⁻¹*A)) (asFreeWord w) :=
        (lift_asFreeWord h (h⁻¹*A) w).symm
      rw [applyWord_eq,eval_fixedProductWord,he]

theorem raw_relator_point {X Y : Type*} (encode : X → Y)
    (h A : Equiv.Perm X) (hf hi af ai : Y → Y)
    (hhf : ∀ p, hf (encode p) = encode (h p))
    (hhi : ∀ p, hi (encode p) = encode (h.symm p))
    (haf : ∀ p, af (encode p) = encode (A p))
    (hai : ∀ p, ai (encode p) = encode (A.symm p))
    (w : List Letter) (hr : FreeGroup.lift (pair h (h⁻¹*A)) (asFreeWord w) = 1)
    (p : X) : applyWord hf hi af ai (fixedProductWord w) (encode p) = encode p := by
  rw [raw_word_eq encode h A hf hi af ai hhf hhi haf hai,hr]
  rfl

end SymmetricSubgroupAsymptotics.FixedProductSignedWordPointEncoding
