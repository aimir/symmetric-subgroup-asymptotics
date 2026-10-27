import SymmetricSubgroupAsymptotics.TernaryHeisenbergGeneratorExt
import Mathlib.GroupTheory.OrderOfElement

/-!
An explicit order-eight automorphism of the ACTUAL Heisenberg27 coordinate
group, with a single orbit on its eight nonzero vector coordinates.
The existing multiplication is (a,b,c)(a',b',c')=(a+a',b+b',c+c'+b*a').
For this convention the polynomial correction is a²+ab. In particular the
old commutator [first,second] is third², not third.
No ambient sporadic group, word, representation or model-order premise.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHeisenbergTernarySingerAction
open CFSGHeisenbergCoordinateGroup
abbrev P := ZMod 3
abbrev H := Element P 1
abbrev V := P × P
abbrev MV := Multiplicative V

private theorem element_ext_zero (g h : H)
    (ha : g.a 0=h.a 0) (hb : g.b 0=h.b 0) (hc : g.c=h.c) : g=h := by
  apply Element.ext
  · funext i
    calc
      g.a i=g.a 0 := congrArg g.a (Subsingleton.elim i 0)
      _=h.a 0 := ha
      _=h.a i := congrArg h.a (Subsingleton.elim 0 i)
  · funext i
    calc
      g.b i=g.b 0 := congrArg g.b (Subsingleton.elim i 0)
      _=h.b 0 := hb
      _=h.b i := congrArg h.b (Subsingleton.elim 0 i)
  · exact hc

private theorem scalar_left_b : ∀ a b : P,(2*a+b)+a=b := by decide +kernel
private theorem scalar_right_a : ∀ a b : P,2*b+(a+b)=a := by decide +kernel
private theorem scalar_left_c : ∀ a b c : P,
    2*(2*c+a^2+a*b)+2*a^2+(2*a+b)*a=c := by decide +kernel
private theorem scalar_right_c : ∀ a b c : P,
    2*(2*c+2*b^2+a*b)+b^2+b*(a+b)=c := by decide +kernel

private theorem scalar_mul_c : ∀ a b c d e f : P,
    2*(c+f+b*d)+(a+d)^2+(a+d)*(b+e)=
      (2*c+a^2+a*b)+(2*f+d^2+d*e)+a*(2*d+e) := by decide +kernel

def forward (g : H) : H :=
  ⟨fun i => 2*g.a i+g.b i,g.a,2*g.c+(g.a 0)^2+g.a 0*g.b 0⟩

def backward (g : H) : H :=
  ⟨g.b,fun i => g.a i+g.b i,2*g.c+2*(g.b 0)^2+g.a 0*g.b 0⟩

/-- The inverse is (u,v,w) ↦ (v,u+v,2w+2v²+uv). -/
def singer : MulAut H where
  toFun := forward
  invFun := backward
  left_inv g := by
    apply Element.ext
    · rfl
    · funext i
      exact scalar_left_b (g.a i) (g.b i)
    · exact scalar_left_c (g.a 0) (g.b 0) g.c
  right_inv g := by
    apply Element.ext
    · funext i
      exact scalar_right_a (g.a i) (g.b i)
    · rfl
    · exact scalar_right_c (g.a 0) (g.b 0) g.c
  map_mul' g h := by
    apply Element.ext
    · funext i
      change 2*(g.a i+h.a i)+(g.b i+h.b i)=
        (2*g.a i+g.b i)+(2*h.a i+h.b i)
      ring
    · rfl
    · change 2*(g.c+h.c+dot g.b h.a)+(g.a 0+h.a 0)^2+
        (g.a 0+h.a 0)*(g.b 0+h.b 0)=
          (2*g.c+(g.a 0)^2+g.a 0*g.b 0)+
            (2*h.c+(h.a 0)^2+h.a 0*h.b 0)+dot g.a (fun i => 2*h.a i+h.b i)
      simpa only [dot,Fin.sum_univ_one] using
        scalar_mul_c (g.a 0) (g.b 0) g.c (h.a 0) (h.b 0) h.c

def scalarProjection : H →* MV where
  toFun g := Multiplicative.ofAdd (g.a 0,g.b 0)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem vector_left : ∀ a b : P,(a,(2*a+b)+a)=(a,b) := by decide +kernel
private theorem vector_right : ∀ a b : P,(2*b+(a+b),b)=(a,b) := by decide +kernel

/-- The vector matrix is [[2,1],[1,0]], with inverse [[0,1],[1,1]]. -/
def singerVector : MulAut MV where
  toFun v := Multiplicative.ofAdd (2*v.toAdd.1+v.toAdd.2,v.toAdd.1)
  invFun v := Multiplicative.ofAdd (v.toAdd.2,v.toAdd.1+v.toAdd.2)
  left_inv v := by
    apply Multiplicative.toAdd.injective
    exact vector_left v.toAdd.1 v.toAdd.2
  right_inv v := by
    apply Multiplicative.toAdd.injective
    exact vector_right v.toAdd.1 v.toAdd.2
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    apply Prod.ext
    · change 2*(v.toAdd.1+w.toAdd.1)+(v.toAdd.2+w.toAdd.2)=
        (2*v.toAdd.1+v.toAdd.2)+(2*w.toAdd.1+w.toAdd.2)
      ring
    · rfl

theorem coordinate_compatibility (g : H) :
    ((singer g).a 0,(singer g).b 0)=
      (singerVector (Multiplicative.ofAdd (g.a 0,g.b 0))).toAdd := rfl

theorem projection_compatibility (g : H) :
    scalarProjection (singer g)=singerVector (scalarProjection g) := rfl

theorem scalarProjection_surjective : Function.Surjective scalarProjection := by
  intro v
  exact ⟨⟨fun _ => v.toAdd.1,fun _ => v.toAdd.2,0⟩,rfl⟩

theorem projection_power_compatibility (n : ℕ) (g : H) :
    scalarProjection ((singer^n) g)=
      (singerVector^n) (scalarProjection g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        scalarProjection ((singer^(n+1)) g)=
            scalarProjection (singer ((singer^n) g)) :=
          congrArg (fun a : MulAut H => scalarProjection (a g)) (pow_succ' singer n)
        _=singerVector (scalarProjection ((singer^n) g)) :=
          projection_compatibility _
        _=singerVector ((singerVector^n) (scalarProjection g)) :=
          congrArg singerVector ih
        _=(singerVector^(n+1)) (scalarProjection g) :=
          (congrArg (fun a : MulAut MV => a (scalarProjection g))
            (pow_succ' singerVector n)).symm

theorem singer_first :
    singer TernaryHeisenbergGeneratorExt.first=
      TernaryHeisenbergGeneratorExt.first^2*TernaryHeisenbergGeneratorExt.second*
        TernaryHeisenbergGeneratorExt.third := by
  apply element_ext_zero <;> decide +kernel

theorem singer_second :
    singer TernaryHeisenbergGeneratorExt.second=TernaryHeisenbergGeneratorExt.first := by
  apply element_ext_zero <;> decide +kernel

theorem singer_third :
    singer TernaryHeisenbergGeneratorExt.third=TernaryHeisenbergGeneratorExt.third^2 := by
  apply element_ext_zero <;> decide +kernel

def commutator : H :=
  TernaryHeisenbergGeneratorExt.first*TernaryHeisenbergGeneratorExt.second*
    TernaryHeisenbergGeneratorExt.first⁻¹*TernaryHeisenbergGeneratorExt.second⁻¹

theorem commutator_eq_third_square : commutator=TernaryHeisenbergGeneratorExt.third^2 := by
  apply element_ext_zero <;> decide +kernel

theorem singer_first_commutator_form :
    singer TernaryHeisenbergGeneratorExt.first=
      TernaryHeisenbergGeneratorExt.first^2*TernaryHeisenbergGeneratorExt.second*commutator^2 := by
  apply element_ext_zero <;> decide +kernel

theorem singer_commutator : singer commutator=commutator^2 := by
  simp only [commutator_eq_third_square,map_pow,singer_third]

private theorem eight_first :
    (singer^8) TernaryHeisenbergGeneratorExt.first=TernaryHeisenbergGeneratorExt.first := by
  apply element_ext_zero <;> decide +kernel

private theorem eight_second :
    (singer^8) TernaryHeisenbergGeneratorExt.second=TernaryHeisenbergGeneratorExt.second := by
  apply element_ext_zero <;> decide +kernel

private theorem eight_third :
    (singer^8) TernaryHeisenbergGeneratorExt.third=TernaryHeisenbergGeneratorExt.third := by
  apply element_ext_zero <;> decide +kernel

theorem singer_pow_eight : singer^8=1 := by
  have he : (singer^8).toMonoidHom=MonoidHom.id H :=
    TernaryHeisenbergGeneratorExt.hom_ext _ _ eight_first eight_second eight_third
  apply MulEquiv.ext
  intro g
  exact DFunLike.congr_fun he g

theorem singer_four_ne_one : singer^4≠1 := by
  intro he
  have hcoord := congrArg (fun f : MulAut H => (f TernaryHeisenbergGeneratorExt.first).a 0) he
  have hne : ((singer^4) TernaryHeisenbergGeneratorExt.first).a 0≠
      TernaryHeisenbergGeneratorExt.first.a 0 := by decide +kernel
  exact hne hcoord

theorem singer_order : orderOf singer=8 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 2)
    (show singer^(2^2)≠1 from singer_four_ne_one)
    (show singer^(2^(2+1))=1 from singer_pow_eight)

private theorem vector_eight_pointwise (v : MV) : (singerVector^8) v=v := by
  obtain ⟨g,hg⟩ := scalarProjection_surjective v
  calc
    (singerVector^8) v=(singerVector^8) (scalarProjection g) :=
      congrArg (fun w : MV => (singerVector^8) w) hg.symm
    _=scalarProjection ((singer^8) g) := (projection_power_compatibility 8 g).symm
    _=scalarProjection g :=
      congrArg (fun a : MulAut H => scalarProjection (a g)) singer_pow_eight
    _=v := hg

theorem singerVector_pow_eight : singerVector^8=1 := by
  apply MulEquiv.ext
  intro v
  exact vector_eight_pointwise v

theorem singerVector_four_ne_one : singerVector^4≠1 := by
  intro he
  have hcoord := congrArg
    (fun f : MulAut MV => f (Multiplicative.ofAdd ((1 : P),0))) he
  have hne : (singerVector^4) (Multiplicative.ofAdd ((1 : P),0))≠
      Multiplicative.ofAdd ((1 : P),0) := by decide +kernel
  exact hne hcoord

theorem singerVector_order : orderOf singerVector=8 := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 2)
    (show singerVector^(2^2)≠1 from singerVector_four_ne_one)
    (show singerVector^(2^(2+1))=1 from singerVector_pow_eight)

/-- A bounded, explicit single-generator orbit, not an assumed transitivity input. -/
theorem vector_transitive : ∀ v w : V,v≠0 → w≠0 →
    ∃ k : Fin 8,(singerVector^k.val) (Multiplicative.ofAdd v)=Multiplicative.ofAdd w := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGHeisenbergTernarySingerAction
