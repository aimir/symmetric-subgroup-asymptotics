import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingChain
import Mathlib.Data.Fin.Tuple.Basic

/-! Actual ordered parameter coverage from genuine opposed peels.
Each coordinate is an element of its literal inversion block, conjugated
by the original inverse prefix. No finite enumeration, cardinal equality
or subgroup generation assertion is substituted for coverage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOpposedPeelingOrderedParameters
open CFSGOpposedSubgroupPeeling CFSGOpposedSubgroupPeelingChain
variable {G : Type*} [Group G]

def orderedProduct (w : ℕ → G) : (n : ℕ) → (Fin n → G) → G
  | 0,_ => 1
  | n+1,b => ((wordPrefix w n)⁻¹*b (Fin.last n)*wordPrefix w n)*
      orderedProduct w n (fun i => b i.castSucc)

theorem exists_residual_parameters (U V : Subgroup G) (w : ℕ → G) (n : ℕ)
    (hdis : Disjoint U V)
    (hBR : ∀j<n,inversionPart U V (w j)≤residual U w j)
    (hfactor : ∀j<n,∀x∈U,∃p∈U,∃b∈inversionPart U V (w j),
      x=p*b ∧ w j*p*(w j)⁻¹∈U)
    (x : G) (hx : x∈U) :
    ∃r∈residual U w n,∃b : Fin n → G,
      (∀j,b j∈inversionPart U V (w j.val)) ∧
      x=((wordPrefix w n)⁻¹*r*wordPrefix w n)*orderedProduct w n b := by
  induction n with
  | zero =>
    refine ⟨x,hx,Fin.elim0,?_,?_⟩
    · intro j
      exact Fin.elim0 j
    · simp only [wordPrefix,orderedProduct,inv_one,one_mul,mul_one]
  | succ n ih =>
    have hn : n<n+1 := Nat.lt_succ_self n
    obtain ⟨r,hr,b,hb,he⟩ := ih
      (fun j hj => hBR j (Nat.lt_trans hj hn))
      (fun j hj => hfactor j (Nat.lt_trans hj hn))
    obtain ⟨p,hp⟩ := (peelProduct_bijective U V (residual U w n) (w n)
      (residual_le U w n) (hBR n hn) hdis (hfactor n hn)).surjective ⟨r,hr⟩
    have hrow : (w n)⁻¹*p.1.val*w n*p.2.val=r :=
      congrArg (fun z : residual U w n => z.val) hp
    refine ⟨p.1.val,p.1.property,Fin.snoc b p.2.val,?_,?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.snoc_last,Fin.val_last] using p.2.property
      · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hb i
    · rw [he,←hrow]
      simp only [wordPrefix,orderedProduct,Fin.snoc_last,Fin.snoc_castSucc]
      group

theorem exists_parameters_of_opposition (U V : Subgroup G) (w : ℕ → G) (n : ℕ)
    (hdis : Disjoint U V)
    (hBR : ∀j<n,inversionPart U V (w j)≤residual U w j)
    (hfactor : ∀j<n,∀x∈U,∃p∈U,∃b∈inversionPart U V (w j),
      x=p*b ∧ w j*p*(w j)⁻¹∈U)
    (hopp : U.map (MulAut.conj (wordPrefix w n)).toMonoidHom≤V)
    (x : G) (hx : x∈U) :
    ∃b : Fin n → G,(∀j,b j∈inversionPart U V (w j.val)) ∧
      x=orderedProduct w n b := by
  obtain ⟨r,hr,b,hb,he⟩ := exists_residual_parameters U V w n hdis hBR hfactor x hx
  have hr1 : r=1 := by
    rw [residual_eq_bot_of_opposition U V w n hdis hopp] at hr
    exact hr
  refine ⟨b,hb,?_⟩
  simpa only [hr1,mul_one,inv_mul_cancel,one_mul] using he

end SymmetricSubgroupAsymptotics.CFSGOpposedPeelingOrderedParameters
