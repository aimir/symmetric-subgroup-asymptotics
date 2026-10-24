import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeeling
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Recursive genuine opposed peels. Every residual retains all earlier
intersection conditions. Prefix containment only supplies the terminal
opposition argument; it is not asserted to be equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingChain
open CFSGOpposedSubgroupPeeling
variable {G : Type*} [Group G]

def residual (U : Subgroup G) (w : ℕ → G) : ℕ → Subgroup G
  | 0 => U
  | n+1 => remainderPart U (residual U w n) (w n)

def wordPrefix (w : ℕ → G) : ℕ → G
  | 0 => 1
  | n+1 => w n * wordPrefix w n

theorem residual_le (U : Subgroup G) (w : ℕ → G) (n : ℕ) :
    residual U w n ≤ U := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact inf_le_left

theorem residual_le_prefix (U : Subgroup G) (w : ℕ → G) (n : ℕ) :
    residual U w n ≤ U.map (MulAut.conj (wordPrefix w n)).toMonoidHom := by
  induction n with
  | zero =>
    intro x hx
    exact ⟨x,hx,by change 1*x*1⁻¹=x; simp⟩
  | succ n ih =>
    intro r hr
    obtain ⟨x,hx,he⟩ := hr.2
    obtain ⟨y,hy,hye⟩ := ih hx
    change w n*x*(w n)⁻¹=r at he
    change wordPrefix w n*y*(wordPrefix w n)⁻¹=x at hye
    refine ⟨y,hy,?_⟩
    change (w n*wordPrefix w n)*y*(w n*wordPrefix w n)⁻¹=r
    calc
      _=w n*(wordPrefix w n*y*(wordPrefix w n)⁻¹)*(w n)⁻¹ := by group
      _=w n*x*(w n)⁻¹ := by rw [hye]
      _=r := he

theorem residual_eq_bot_of_opposition (U V : Subgroup G) (w : ℕ → G) (n : ℕ)
    (hdis : Disjoint U V)
    (hopp : U.map (MulAut.conj (wordPrefix w n)).toMonoidHom ≤ V) :
    residual U w n = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x=1
  exact Subgroup.disjoint_def.mp hdis (residual_le U w n hx)
    (hopp (residual_le_prefix U w n hx))

theorem card_eq_residual_mul_blocks [Finite G] (U V : Subgroup G) (w : ℕ → G)
    (n : ℕ) (hdis : Disjoint U V)
    (hBR : ∀ j<n, inversionPart U V (w j) ≤ residual U w j)
    (hfactor : ∀ j<n, ∀ x∈U, ∃ p∈U, ∃ b∈inversionPart U V (w j),
      x=p*b ∧ w j*p*(w j)⁻¹∈U) :
    Nat.card U = Nat.card (residual U w n) *
      ∏ j∈Finset.range n, Nat.card (inversionPart U V (w j)) := by
  induction n with
  | zero => simp only [residual,Finset.range_zero,Finset.prod_empty,mul_one]
  | succ n ih =>
    have hn : n<n+1 := Nat.lt_succ_self n
    have hi := ih (fun j hj => hBR j (Nat.lt_trans hj hn))
      (fun j hj => hfactor j (Nat.lt_trans hj hn))
    have hs := card_eq_remainder_mul_inversion U V (residual U w n) (w n)
      (residual_le U w n) (hBR n hn) hdis (hfactor n hn)
    change Nat.card (residual U w n) = Nat.card (residual U w (n+1)) *
      Nat.card (inversionPart U V (w n)) at hs
    rw [hi,hs,Finset.prod_range_succ]
    ac_rfl

theorem card_eq_blocks_of_opposition [Finite G] (U V : Subgroup G) (w : ℕ → G)
    (n : ℕ) (hdis : Disjoint U V)
    (hBR : ∀ j<n, inversionPart U V (w j) ≤ residual U w j)
    (hfactor : ∀ j<n, ∀ x∈U, ∃ p∈U, ∃ b∈inversionPart U V (w j),
      x=p*b ∧ w j*p*(w j)⁻¹∈U)
    (hopp : U.map (MulAut.conj (wordPrefix w n)).toMonoidHom ≤ V) :
    Nat.card U = ∏ j∈Finset.range n, Nat.card (inversionPart U V (w j)) := by
  have h := card_eq_residual_mul_blocks U V w n hdis hBR hfactor
  rw [residual_eq_bot_of_opposition U V w n hdis hopp,Subgroup.card_bot,one_mul] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingChain
