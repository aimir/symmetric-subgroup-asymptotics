import SymmetricSubgroupAsymptotics.DerivedGeneratorWords
import SymmetricSubgroupAsymptotics.BinaryPairAffineChart

/-! Literal signed words bind sparse offset rows to the actual original
group. Derived words are flattened by a proved identity, so commutator
membership never depends on a producer's exponent-sum flag. -/
set_option autoImplicit false
noncomputable section
open scoped Classical commutatorElement

namespace SymmetricSubgroupAsymptotics.BinarySignedOffsetWord

abbrev Letter (J : Type*) := J × Bool

def letterEval {J G : Type*} [Group G] (u : J → G) (l : Letter J) : G :=
  if l.2 then u l.1 else (u l.1)⁻¹

def eval {J G : Type*} [Group G] (u : J → G) (w : List (Letter J)) : G :=
  (w.map (letterEval u)).prod

def inverse {J : Type*} (w : List (Letter J)) : List (Letter J) :=
  w.reverse.map fun l => (l.1, !l.2)

theorem eval_append {J G : Type*} [Group G]
    (u : J → G) (a b : List (Letter J)) :
    eval u (a ++ b) = eval u a * eval u b := by
  simp only [eval, List.map_append, List.prod_append]

theorem eval_inverse {J G : Type*} [Group G]
    (u : J → G) (w : List (Letter J)) : eval u (inverse w) = (eval u w)⁻¹ := by
  have hletter : (letterEval u) ∘ (fun l : Letter J => (l.1, !l.2)) =
      fun l => (letterEval u l)⁻¹ := by
    funext l
    rcases l with ⟨i, b⟩
    cases b <;> simp [letterEval]
  simp only [eval, inverse, List.map_map, hletter]
  rw [List.map_reverse, List.prod_inv_reverse, List.map_map]
  rfl

theorem map_eval {J G Q : Type*} [Group G] [Group Q]
    (f : G →* Q) (u : J → G) (w : List (Letter J)) :
    f (eval u w) = eval (fun j => f (u j)) w := by
  induction w with
  | nil => simp [eval]
  | cons l w ih =>
      change f (letterEval u l * eval u w) =
        letterEval (fun j => f (u j)) l * eval (fun j => f (u j)) w
      rw [map_mul, ih]
      congr 1
      rcases l with ⟨i, b⟩
      cases b <;> simp [letterEval, map_inv]

def ofDerived {J : Type*} : DerivedGeneratorWord J → List (Letter J)
  | .one => []
  | .comm i j => [(i, true), (j, true), (i, false), (j, false)]
  | .mul a b => ofDerived a ++ ofDerived b
  | .inv a => inverse (ofDerived a)
  | .conj i a => [(i, true)] ++ ofDerived a ++ [(i, false)]
  | .conjInv i a => [(i, false)] ++ ofDerived a ++ [(i, true)]

theorem eval_ofDerived {J G : Type*} [Group G]
    (w : DerivedGeneratorWord J) (u : J → G) : eval u (ofDerived w) = w.eval u := by
  induction w with
  | one => simp [ofDerived, eval, DerivedGeneratorWord.eval]
  | comm i j => simp [ofDerived, eval, letterEval, DerivedGeneratorWord.eval,
      commutatorElement_def, mul_assoc]
  | mul a b ha hb => simp only [ofDerived, eval_append, ha, hb, DerivedGeneratorWord.eval]
  | inv a ha => simp only [ofDerived, eval_inverse, ha, DerivedGeneratorWord.eval]
  | conj i a ha =>
      change eval u ([(i, true)] ++ ofDerived a ++ [(i, false)]) =
        u i * a.eval u * (u i)⁻¹
      rw [eval_append, eval_append, ha]
      simp [eval, letterEval]
  | conjInv i a ha =>
      change eval u ([(i, false)] ++ ofDerived a ++ [(i, true)]) =
        (u i)⁻¹ * a.eval u * u i
      rw [eval_append, eval_append, ha]
      simp [eval, letterEval]

theorem eval_ofDerived_mem_commutator {J G : Type*} [Group G]
    (w : DerivedGeneratorWord J) (u : J → G) :
    eval u (ofDerived w) ∈ commutator G := by
  rw [eval_ofDerived]
  exact w.eval_mem_commutator u

def projection {J I : Type*} (j : J) : (J → I → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) where
  toFun v := v j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def reindex {I : Type*} (g : Equiv.Perm I) : (I → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) where
  toFun v := v ∘ g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def letterOffset {J I : Type*} (p : J → Equiv.Perm I) (l : Letter J) :
    (J → I → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2) :=
  if l.2 then projection l.1 else - (reindex (p l.1)⁻¹).comp (projection l.1)

def offset {J I : Type*} (p : J → Equiv.Perm I) : List (Letter J) →
    ((J → I → ZMod 2) →ₗ[ZMod 2] (I → ZMod 2))
  | [] => 0
  | l :: w => offset p w + (reindex (eval p w)).comp (letterOffset p l)

variable {J X I : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

theorem original_offset_one (i : I) : F.offset 1 i = 0 := by
  change (F.frame.symm (F.frame (i, 0))).2 = 0
  rw [F.frame.symm_apply_apply]

theorem original_offset_inv (u : U) (i : I) :
    F.offset u⁻¹ i = - F.offset u ((F.top u)⁻¹ i) := by
  have he := F.offset_mul u u⁻¹ i
  rw [mul_inv_cancel, original_offset_one, map_inv] at he
  exact eq_neg_of_add_eq_zero_left he.symm

theorem letterOffset_original (u : J → U) (p : J → Equiv.Perm I)
    (hp : ∀ j, F.top (u j) = p j) (l : Letter J) :
    letterOffset p l (fun j => F.offset (u j)) = F.offset (letterEval u l) := by
  rcases l with ⟨j, b⟩
  cases b <;> ext i <;>
    simp [letterOffset, letterEval, projection, reindex, original_offset_inv, hp]

/-- Sparse word-offset rows represent the actual original product, with
the original top permutation and the actual offsets of its chosen lifts. -/
theorem offset_original (u : J → U) (p : J → Equiv.Perm I)
    (hp : ∀ j, F.top (u j) = p j) (w : List (Letter J)) :
    offset p w (fun j => F.offset (u j)) = F.offset (eval u w) := by
  induction w with
  | nil =>
      ext i
      simp only [offset, LinearMap.zero_apply, Pi.zero_apply, eval,
        List.map_nil, List.prod_nil, original_offset_one]
  | cons l w ih =>
      have ht : F.top (eval u w) = eval p w := by
        rw [map_eval]
        congr 1
        exact funext hp
      have hl := letterOffset_original F u p hp l
      ext i
      change offset p w (fun j => F.offset (u j)) i +
        letterOffset p l (fun j => F.offset (u j)) (eval p w i) =
          F.offset (letterEval u l * eval u w) i
      rw [ih, hl, F.offset_mul, ht]

end SymmetricSubgroupAsymptotics.BinarySignedOffsetWord
