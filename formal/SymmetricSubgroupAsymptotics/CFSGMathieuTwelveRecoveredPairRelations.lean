import SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePresentationWords
import SymmetricSubgroupAsymptotics.InvolutionTernaryProductShortRecovery

/-! Necessary equations for automorphisms of the SAME original M12 fixing
A=x*y. The variable u is the image of x*A*x^-1. Short recovery reconstructs
the images of x and y. The six pinned relators and the separate product
link are necessary only; no presentation converse or capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelveRecoveredPairRelations
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelvePresentationWords

def firstElement : M12 := x * y
def secondElement : M12 := x * firstElement * x⁻¹

def recoverX {G : Type*} [Group G] (a u : G) : G := a⁻¹ * u⁻¹ * a⁻¹
def recoverY {G : Type*} [Group G] (a u : G) : G := a⁻¹ * u⁻¹

theorem recover_originalX : recoverX firstElement secondElement = x :=
  InvolutionTernaryProductShortRecovery.recover_first x y relator_zero relator_one

theorem recover_originalY : recoverY firstElement secondElement = y :=
  InvolutionTernaryProductShortRecovery.recover_second x y relator_zero relator_one

def relationValue {G : Type*} [Group G] (r : Fin 7) (a u : G) : G :=
  let v := recoverX a u
  let w := recoverY a u
  match r.val with
  | 0 => v ^ 2
  | 1 => w ^ 3
  | 2 => (v * w) ^ 11
  | 3 => (v⁻¹ * w⁻¹ * v * w) ^ 6
  | 4 => (v * w * v * w * v * w⁻¹) ^ 6
  | 5 => (v⁻¹ * (w * v * w)⁻¹ * v * (w * v * w)) ^ 5
  | _ => v * w

def relationTarget {G : Type*} [Group G] (r : Fin 7) (a : G) : G :=
  if r.val = 6 then a else 1

theorem relationValue_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (r : Fin 7) (a u : G) :
    f (relationValue r a u) = relationValue r (f a) (f u) := by
  fin_cases r <;> simp only [relationValue,recoverX,recoverY,map_pow,map_mul,map_inv]

theorem relationTarget_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (r : Fin 7) (a : G) :
    f (relationTarget r a) = relationTarget r (f a) := by
  unfold relationTarget
  split <;> simp only [map_one]

theorem relationValue_coe (r : Fin 7) (a u : M12) :
    (relationValue r a u).val = relationValue r a.val u.val :=
  relationValue_map M12Subgroup.subtype r a u

theorem relationTarget_coe (r : Fin 7) (a : M12) :
    (relationTarget r a).val = relationTarget r a.val :=
  relationTarget_map M12Subgroup.subtype r a

theorem original_pair_relations (r : Fin 7) :
    relationValue r firstElement secondElement = relationTarget r firstElement := by
  have hx := recover_originalX
  have hy := recover_originalY
  fin_cases r <;> simp only [relationValue,relationTarget,show (0 : ℕ) ≠ 6 by decide,
    show (1 : ℕ) ≠ 6 by decide,show (2 : ℕ) ≠ 6 by decide,
    show (3 : ℕ) ≠ 6 by decide,show (4 : ℕ) ≠ 6 by decide,
    show (5 : ℕ) ≠ 6 by decide,ite_false,ite_true,hx,hy]
  · exact relator_zero
  · exact relator_one
  · exact relator_two
  · exact relator_three
  · simpa only [pow_one] using relator_four
  · exact relator_five
  · rfl

def Accepts (u : M12) : Prop :=
  ∀ r : Fin 7, relationValue r firstElement u = relationTarget r firstElement

theorem accepts_of_fixed_first (f : MulAut M12)
    (hf : f firstElement = firstElement) : Accepts (f secondElement) := by
  intro r
  have h := congrArg f (original_pair_relations r)
  change f.toMonoidHom (relationValue r firstElement secondElement) =
    f.toMonoidHom (relationTarget r firstElement) at h
  rw [relationValue_map f.toMonoidHom,relationTarget_map f.toMonoidHom] at h
  have hf' : f.toMonoidHom firstElement = firstElement := hf
  rw [hf'] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelveRecoveredPairRelations
