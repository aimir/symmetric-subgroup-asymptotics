import Mathlib.Data.Quot
import Mathlib.Data.Finite.Card
import Mathlib.Algebra.Group.End

/-! The actual unordered-pair quotient of a fixed-point-free involution.
A chosen representative supplies an injection of quotient×Bool into the
original carrier. Permutations commuting with the involution descend. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.FreeInvolutionPairQuotient

variable {X : Type} (ι : X→X) (hι : Function.Involutive ι)

def pairSetoid : Setoid X where
  r x y := x=y ∨ x=ι y
  iseqv := by
    refine ⟨fun _=>Or.inl rfl,?_,?_⟩
    · intro x y h
      rcases h with h|h
      · exact Or.inl h.symm
      · exact Or.inr ((hι y).symm.trans (congrArg ι h.symm))
    · intro x y z hxy hyz
      rcases hxy with rfl|hxy
      · exact hyz
      rcases hyz with rfl|hyz
      · exact Or.inr hxy
      · exact Or.inl (hxy.trans ((congrArg ι hyz).trans (hι z)))

abbrev Pairs := Quotient (pairSetoid ι hι)

def mk (x : X) : Pairs ι hι := Quotient.mk _ x

theorem mk_eq_mk (x y : X) : mk ι hι x=mk ι hι y ↔ x=y ∨ x=ι y :=
  Quotient.eq

private def fibreLift (q : Pairs ι hι) (b : Bool) : X := if b then q.out else ι q.out

private theorem mk_fibreLift (q : Pairs ι hι) (b : Bool) :
    mk ι hι (fibreLift ι hι q b)=q := by
  cases b
  · change mk ι hι (ι q.out)=q
    exact (Quotient.sound (show (pairSetoid ι hι).r (ι q.out) q.out from Or.inr rfl)).trans
      (Quotient.out_eq q)
  · exact Quotient.out_eq q

theorem two_mul_card_le [Finite X] (hfree : ∀x,ι x≠x) :
    2*Nat.card (Pairs ι hι)≤Nat.card X := by
  have hinj : Function.Injective (fun z:Pairs ι hι × Bool=>fibreLift ι hι z.1 z.2) := by
    rintro ⟨q,b⟩ ⟨r,c⟩ he
    have hqr : q=r := (mk_fibreLift ι hι q b).symm.trans
      ((congrArg (mk ι hι) he).trans (mk_fibreLift ι hι r c))
    subst r
    have hbc : b=c := by
      cases b <;> cases c
      · rfl
      · exact (hfree q.out he).elim
      · exact (hfree q.out he.symm).elim
      · rfl
    exact congrArg (fun b:Bool=>(q,b)) hbc
  have hh := Nat.card_le_card_of_injective _ hinj
  have hb : Nat.card Bool=2 := by simp
  simpa only [Nat.card_prod,hb,Nat.mul_comm] using hh

def pairPermutation (e : Equiv.Perm X) (he : ∀x,e (ι x)=ι (e x)) :
    Equiv.Perm (Pairs ι hι) :=
  Quotient.congr e (by
    intro x y
    change (x=y ∨ x=ι y) ↔ (e x=e y ∨ e x=ι (e y))
    rw [←he y]
    constructor
    · exact Or.imp (congrArg e) (congrArg e)
    · exact Or.imp (fun h=>e.injective h) (fun h=>e.injective h))

theorem pairPermutation_mk (e : Equiv.Perm X) (he : ∀x,e (ι x)=ι (e x)) (x : X) :
    pairPermutation ι hι e he (mk ι hι x)=mk ι hι (e x) := rfl

def pairHom {H : Type} [Group H] (φ : H→*Equiv.Perm X)
    (hφ : ∀h x,φ h (ι x)=ι (φ h x)) : H→*Equiv.Perm (Pairs ι hι) where
  toFun h := pairPermutation ι hι (φ h) (hφ h)
  map_one' := by
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change mk ι hι (φ 1 x)=mk ι hι x
    rw [map_one]
    rfl
  map_mul' h k := by
    apply Equiv.ext
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change mk ι hι (φ (h*k) x)=mk ι hι (φ h (φ k x))
    rw [map_mul]
    rfl

theorem pairHom_mk {H : Type} [Group H] (φ : H→*Equiv.Perm X)
    (hφ : ∀h x,φ h (ι x)=ι (φ h x)) (h : H) (x : X) :
    pairHom ι hι φ hφ h (mk ι hι x)=mk ι hι (φ h x) := rfl

end SymmetricSubgroupAsymptotics.FreeInvolutionPairQuotient
