import Mathlib.Algebra.Group.Hom.End
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finite.Card

/-! An injective finite scalar ring normalized by an actual ring
conjugation acquires an actual ring AUTOMORPHISM. Finiteness upgrades
the proved injective endomorphism; a field automorphism is not supplied
as an input. Additive conjugation on endomorphisms is literal. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGFiniteScalarConjugation

variable {A : Type*} [AddCommGroup A]

def additiveConjugation (E : A ≃+ A) : AddMonoid.End A ≃+* AddMonoid.End A where
  toFun f := E.toAddMonoidHom.comp (f.comp E.symm.toAddMonoidHom)
  invFun f := E.symm.toAddMonoidHom.comp (f.comp E.toAddMonoidHom)
  left_inv f := by
    apply AddMonoidHom.ext
    intro x
    change E.symm (E (f (E.symm (E x)))) = f x
    simp only [E.symm_apply_apply]
  right_inv f := by
    apply AddMonoidHom.ext
    intro x
    change E (E.symm (f (E (E.symm x)))) = f x
    simp only [E.apply_symm_apply]
  map_mul' f g := by
    apply AddMonoidHom.ext
    intro x
    change E (f (g (E.symm x))) = E (f (E.symm (E (g (E.symm x)))))
    rw [E.symm_apply_apply]
  map_add' f g := by
    apply AddMonoidHom.ext
    intro x
    change E (f (E.symm x) + g (E.symm x)) = E (f (E.symm x)) + E (g (E.symm x))
    exact map_add E _ _

section Ring
variable {R S : Type*} [Semiring R] [Semiring S]

def descendedHom (i : R →+* S) (hi : Function.Injective i) (e : S ≃+* S)
    (h : ∀ a : R, ∃ b : R, e (i a) = i b) : R →+* R where
  toFun a := Classical.choose (h a)
  map_zero' := by
    apply hi
    calc
      i (Classical.choose (h 0)) = e (i 0) := (Classical.choose_spec (h 0)).symm
      _ = i 0 := by simp only [map_zero]
  map_one' := by
    apply hi
    calc
      i (Classical.choose (h 1)) = e (i 1) := (Classical.choose_spec (h 1)).symm
      _ = i 1 := by simp only [map_one]
  map_add' a b := by
    apply hi
    calc
      i (Classical.choose (h (a + b))) = e (i (a + b)) := (Classical.choose_spec (h (a + b))).symm
      _ = e (i a + i b) := congrArg e (i.map_add a b)
      _ = e (i a) + e (i b) := e.map_add (i a) (i b)
      _ = i (Classical.choose (h a)) + i (Classical.choose (h b)) :=
        congrArg₂ (fun x y : S => x + y) (Classical.choose_spec (h a)) (Classical.choose_spec (h b))
      _ = i (Classical.choose (h a) + Classical.choose (h b)) := (i.map_add _ _).symm
  map_mul' a b := by
    apply hi
    calc
      i (Classical.choose (h (a * b))) = e (i (a * b)) := (Classical.choose_spec (h (a * b))).symm
      _ = e (i a * i b) := congrArg e (i.map_mul a b)
      _ = e (i a) * e (i b) := e.map_mul (i a) (i b)
      _ = i (Classical.choose (h a)) * i (Classical.choose (h b)) :=
        congrArg₂ (fun x y : S => x * y) (Classical.choose_spec (h a)) (Classical.choose_spec (h b))
      _ = i (Classical.choose (h a) * Classical.choose (h b)) := (i.map_mul _ _).symm

theorem descendedHom_spec (i : R →+* S) (hi : Function.Injective i) (e : S ≃+* S)
    (h : ∀ a : R, ∃ b : R, e (i a) = i b) (a : R) :
    e (i a) = i (descendedHom i hi e h a) := Classical.choose_spec (h a)

theorem descendedHom_injective (i : R →+* S) (hi : Function.Injective i) (e : S ≃+* S)
    (h : ∀ a : R, ∃ b : R, e (i a) = i b) : Function.Injective (descendedHom i hi e h) := by
  intro a b hab
  apply hi
  apply e.injective
  calc
    e (i a) = i (descendedHom i hi e h a) := descendedHom_spec i hi e h a
    _ = i (descendedHom i hi e h b) := congrArg i hab
    _ = e (i b) := (descendedHom_spec i hi e h b).symm

def descendedEquiv [Finite R] (i : R →+* S) (hi : Function.Injective i) (e : S ≃+* S)
    (h : ∀ a : R, ∃ b : R, e (i a) = i b) : R ≃+* R :=
  RingEquiv.ofBijective (descendedHom i hi e h)
    ⟨descendedHom_injective i hi e h, Finite.surjective_of_injective (descendedHom_injective i hi e h)⟩

theorem descendedEquiv_spec [Finite R] (i : R →+* S) (hi : Function.Injective i) (e : S ≃+* S)
    (h : ∀ a : R, ∃ b : R, e (i a) = i b) (a : R) :
    e (i a) = i (descendedEquiv i hi e h a) := descendedHom_spec i hi e h a

end Ring
end SymmetricSubgroupAsymptotics.CFSGFiniteScalarConjugation
