import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.ZMod.Basic

/-! Actual directed edges of the four vertices, with a separate central
orientation reversal. No group-order label or generated-group census. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row22DirectedEdgeModel
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
abbrev Bit := Multiplicative (ZMod 2)
abbrev Model := Equiv.Perm (Fin 4) × Bit

def label (x : Fin 12) : Fin 4 × Fin 4 :=
  (#[(0,3),(1,3),(1,0),(2,0),(0,1),(2,1),
     (3,1),(1,2),(3,0),(0,2),(2,3),(3,2)] : Array (Fin 4 × Fin 4))[x.val]!
def point (a b : Fin 4) : Fin 12 :=
  (#[0,4,9,0,2,0,7,1,3,5,0,10,8,6,11,0] : Array (Fin 12))[4*a.val+b.val]!
def forward (g : Model) (x : Fin 12) : Fin 12 :=
  if g.2=1 then point (g.1 (label x).1) (g.1 (label x).2)
  else point (g.1 (label x).2) (g.1 (label x).1)

private def pairForward (g : Model) (x : Fin 4 × Fin 4) : Fin 4 × Fin 4 :=
  if g.2=1 then (g.1 x.1,g.1 x.2) else (g.1 x.2,g.1 x.1)
private theorem pair_one (x : Fin 4 × Fin 4) : pairForward 1 x=x := by
  rcases x with ⟨a,b⟩
  rfl
private theorem pair_mul (g h : Model) (x : Fin 4 × Fin 4) :
    pairForward (g*h) x=pairForward g (pairForward h x) := by
  have hc : ∀ z : Bit,z=1 ∨ z=Multiplicative.ofAdd 1 := by decide +kernel
  have hs : (Multiplicative.ofAdd (1 : ZMod 2)) * Multiplicative.ofAdd 1 = 1 := by decide +kernel
  have hn : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide +kernel
  rcases g with ⟨p,z⟩
  rcases h with ⟨q,w⟩
  rcases hc z with rfl | rfl <;> rcases hc w with rfl | rfl <;>
    simp [pairForward,Equiv.Perm.mul_apply,hs,hn]

private theorem label_point : ∀ a b : Fin 4,a≠b → label (point a b)=(a,b) := by
  decide +kernel
private theorem label_ne : ∀ x : Fin 12,(label x).1≠(label x).2 := by decide +kernel
private theorem label_injective : Function.Injective label := by
  have h : ∀ x : Fin 12,point (label x).1 (label x).2=x := by decide +kernel
  intro x y he
  exact (h x).symm.trans ((congrArg (fun z : Fin 4 × Fin 4 => point z.1 z.2) he).trans (h y))
private theorem label_forward (g : Model) (x : Fin 12) :
    label (forward g x)=pairForward g (label x) := by
  by_cases hz : g.2=1
  · simp only [forward,pairForward,hz,if_true]
    exact label_point _ _ (fun h => label_ne x (g.1.injective h))
  · simp only [forward,pairForward,hz,if_false]
    exact label_point _ _ (fun h => label_ne x (g.1.injective h).symm)

def permutation (g : Model) : Equiv.Perm (Fin 12) where
  toFun := forward g
  invFun := forward g⁻¹
  left_inv x := by
    apply label_injective
    rw [label_forward,label_forward,← pair_mul,inv_mul_cancel,pair_one]
  right_inv x := by
    apply label_injective
    rw [label_forward,label_forward,← pair_mul,mul_inv_cancel,pair_one]

def action : Model →* Equiv.Perm (Fin 12) where
  toFun := permutation
  map_one' := by
    apply Equiv.ext
    intro x
    apply label_injective
    change label (forward 1 x)=label x
    rw [label_forward,pair_one]
  map_mul' g h := by
    apply Equiv.ext
    intro x
    apply label_injective
    change label (forward (g*h) x)=label (forward g (forward h x))
    rw [label_forward,label_forward,label_forward,pair_mul]

def codes : Fin 3 → Model :=
  ![(Equiv.swap 0 1,1),(finRotate 4,1),(1,Multiplicative.ofAdd 1)]

theorem generator_eq : ∀ i : Fin 3, action (codes i)=row22Generators i := by
  intro i
  apply Equiv.ext
  revert i
  decide +kernel

theorem action_injective : Function.Injective action := by
  have hker : ∀ g : Model,(∀ x : Fin 12,action g x=x) → g=1 := by decide +kernel
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_antisymm
  · intro g hg
    change g=1
    apply hker
    intro x
    exact congrArg (fun p : Equiv.Perm (Fin 12) => p x) (show action g=1 from hg)
  · exact bot_le
end SymmetricSubgroupAsymptotics.Row22DirectedEdgeModel
