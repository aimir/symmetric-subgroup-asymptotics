import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! A literal twisted monomial action admits frame/root coordinates on
nonabelian1-cocycles. The coordinate twists are retained throughout.
This proves only the injection and its finite count; no root epimorphism
restriction, local fibre capacity or global LMM bound is assumed/proved. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFrame

/-- Nonabelian cocycles for the displayed actual automorphism action. -/
abbrev Cocycle {P B : Type*} [Group P] [Group B] (alpha : P →* MulAut B) :=
  {c : P → B // ∀ p q : P, c (p*q)=c p*alpha p (c q)}

variable {Q X A : Type*} [Group Q] [Group A] [MulAction Q X]
variable (rho : Q →* MulAut (X → A)) (theta : Q → X → MulAut A)
variable (hcoord : ∀ q : Q, ∀ f : X → A, ∀ x : X,
  (rho q f) (q • x)=theta q x (f x))

include rho hcoord in
/-- The literal coordinate formula forces the twist multiplication law;
it is not a separate untwisted-action hypothesis. -/
theorem twist_mul (q r : Q) (x : X) :
    theta (q*r) x=theta q (r • x)*theta r x := by
  apply MulEquiv.ext
  intro a
  change theta (q*r) x a=theta q (r • x) (theta r x a)
  calc
    theta (q*r) x a=(rho (q*r) (fun _ : X => a)) ((q*r) • x) :=
      (hcoord (q*r) (fun _ : X => a) x).symm
    _=(rho q (rho r (fun _ : X => a))) (q • (r • x)) := by
      rw [map_mul,mul_smul]
      rfl
    _=theta q (r • x) ((rho r (fun _ : X => a)) (r • x)) :=
      hcoord q (rho r (fun _ : X => a)) (r • x)
    _=theta q (r • x) (theta r x a) :=
      congrArg (theta q (r • x)) (hcoord r (fun _ : X => a) x)

include rho hcoord in
theorem twist_one (x : X) : theta 1 x=1 := by
  apply MulEquiv.ext
  intro a
  have h := hcoord 1 (fun _ : X => a) x
  simpa only [map_one,MulAut.one_apply,one_smul] using h.symm

/-- The root action is the actual twist on the actual point stabilizer. -/
def rootAction (x0 : X) : MulAction.stabilizer Q x0 →* MulAut A where
  toFun h := theta (h : Q) x0
  map_one' := twist_one rho theta hcoord x0
  map_mul' h k := by
    change theta ((h : Q)*(k : Q)) x0=theta (h : Q) x0*theta (k : Q) x0
    rw [twist_mul rho theta hcoord]
    have hk : (k : Q) • x0=x0 := k.property
    rw [hk]

def rootRestriction (x0 : X) (c : Cocycle rho) :
    Cocycle (rootAction rho theta hcoord x0) :=
  ⟨fun h => c.val (h : Q) x0,by
    intro h k
    have hh : (h : Q) • x0=x0 := h.property
    have hc : (rho (h : Q) (c.val (k : Q))) x0=
        theta (h : Q) x0 (c.val (k : Q) x0) := by
      simpa only [hh] using hcoord (h : Q) (c.val (k : Q)) x0
    change c.val ((h : Q)*(k : Q)) x0=
      c.val (h : Q) x0*theta (h : Q) x0 (c.val (k : Q) x0)
    exact (congrFun (c.property (h : Q) (k : Q)) x0).trans
      (congrArg (fun a : A => c.val (h : Q) x0*a) hc)⟩

def frame (t : X → Q) (c : Cocycle rho) : X → A := fun x => c.val (t x) x

/-- The actual Schreier element lies in the actual root stabilizer. -/
def schreierElement (x0 : X) (t : X → Q) (ht : ∀ x : X, t x • x0=x)
    (q : Q) (x : X) : MulAction.stabilizer Q x0 :=
  ⟨(t (q • x))⁻¹*q*t x,by
    change ((t (q • x))⁻¹*q*t x) • x0=x0
    calc
      _=(t (q • x))⁻¹ • (q • (t x • x0)) := by rw [mul_smul,mul_smul]
      _=(t (q • x))⁻¹ • (q • x) := by rw [ht x]
      _=(t (q • x))⁻¹ • (t (q • x) • x0) :=
        congrArg (fun y : X => (t (q • x))⁻¹ • y) (ht (q • x)).symm
      _=x0 := inv_smul_smul _ _⟩

/-- Recovery retains BOTH actual coordinate twists. No value at the root
of the transversal is normalized or assumed to be1. -/
theorem recovery (x0 : X) (t : X → Q) (ht : ∀ x : X, t x • x0=x)
    (c : Cocycle rho) (q : Q) (x : X) :
    c.val q (q • x)=
      frame rho t c (q • x)*
        theta (t (q • x)) x0
          ((rootRestriction rho theta hcoord x0 c).val (schreierElement x0 t ht q x))*
        (theta q x (frame rho t c x))⁻¹ := by
  let h : MulAction.stabilizer Q x0 := schreierElement x0 t ht q x
  have hpath : q*t x=t (q • x)*(h : Q) := by
    dsimp only [h,schreierElement]
    simp only [mul_assoc,mul_inv_cancel_left]
  have hleft : c.val (q*t x) (q • x)=
      c.val q (q • x)*theta q x (frame rho t c x) := by
    exact (congrFun (c.property q (t x)) (q • x)).trans
      (congrArg (fun a : A => c.val q (q • x)*a) (hcoord q (c.val (t x)) x))
  have hc : (rho (t (q • x)) (c.val (h : Q))) (q • x)=
      theta (t (q • x)) x0 (c.val (h : Q) x0) := by
    simpa only [ht (q • x)] using hcoord (t (q • x)) (c.val (h : Q)) x0
  have hright : c.val (t (q • x)*(h : Q)) (q • x)=
      frame rho t c (q • x)*theta (t (q • x)) x0 (c.val (h : Q) x0) :=
    (congrFun (c.property (t (q • x)) (h : Q)) (q • x)).trans
      (congrArg (fun a : A => frame rho t c (q • x)*a) hc)
  have he : c.val q (q • x)*theta q x (frame rho t c x)=
      frame rho t c (q • x)*theta (t (q • x)) x0 (c.val (h : Q) x0) := by
    calc
      _=c.val (q*t x) (q • x) := hleft.symm
      _=c.val (t (q • x)*(h : Q)) (q • x) :=
        congrArg (fun z : Q => c.val z (q • x)) hpath
      _=_ := hright
  have he' := congrArg (fun a : A => a*(theta q x (frame rho t c x))⁻¹) he
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using he'

def encode (x0 : X) (t : X → Q) (c : Cocycle rho) :
    (X → A) × Cocycle (rootAction rho theta hcoord x0) :=
  (frame rho t c,rootRestriction rho theta hcoord x0 c)

theorem encode_injective (x0 : X) (t : X → Q) (ht : ∀ x : X, t x • x0=x) :
    Function.Injective (encode rho theta hcoord x0 t) := by
  intro c d he
  have hu : frame rho t c=frame rho t d := congrArg Prod.fst he
  have hr : rootRestriction rho theta hcoord x0 c=rootRestriction rho theta hcoord x0 d :=
    congrArg Prod.snd he
  apply Subtype.ext
  funext q x
  have hh : c.val q (q • (q⁻¹ • x))=d.val q (q • (q⁻¹ • x)) := by
    rw [recovery rho theta hcoord x0 t ht c q (q⁻¹ • x),
      recovery rho theta hcoord x0 t ht d q (q⁻¹ • x),hu,hr]
  simpa only [smul_inv_smul] using hh

/-- Finite count requires finiteness of the target root-cocycle set, not
finiteness of Q itself. The injection above is unrestricted. -/
theorem card_le_frame_root [Finite X] [Finite A] (x0 : X)
    [Finite (Cocycle (rootAction rho theta hcoord x0))]
    (t : X → Q) (ht : ∀ x : X, t x • x0=x) :
    Nat.card (Cocycle rho) ≤
      Nat.card A ^ Nat.card X*Nat.card (Cocycle (rootAction rho theta hcoord x0)) := by
  have h := Nat.card_le_card_of_injective (encode rho theta hcoord x0 t)
    (encode_injective rho theta hcoord x0 t ht)
  simpa only [Nat.card_prod,Nat.card_fun] using h

def transversal [MulAction.IsPretransitive Q X] (x0 : X) (x : X) : Q :=
  Classical.choose (MulAction.exists_smul_eq Q x0 x)

theorem transversal_spec [MulAction.IsPretransitive Q X] (x0 x : X) :
    transversal (Q := Q) x0 x • x0=x :=
  Classical.choose_spec (MulAction.exists_smul_eq Q x0 x)

/-- Convenient finite transitive form, using an actual chosen transversal. -/
theorem card_le_transitive [Finite Q] [Finite X] [Finite A]
    [MulAction.IsPretransitive Q X] (x0 : X) :
    Nat.card (Cocycle rho) ≤
      Nat.card A ^ Nat.card X*Nat.card (Cocycle (rootAction rho theta hcoord x0)) :=
  card_le_frame_root rho theta hcoord x0 (transversal (Q := Q) x0)
    (transversal_spec (Q := Q) x0)

end SymmetricSubgroupAsymptotics.TwistedMonomialCocycleFrame
