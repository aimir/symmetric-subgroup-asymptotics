import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingChain

/-! Reverse actual opposed peels to prove subgroup generation. At each
step the available bijection writes an element of R as w⁻¹*r*w*b,
where r lies in the next residual and b in the genuine inversion block.
No order-formula or root-generator recognition premise is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupReversePeeling
open CFSGOpposedSubgroupPeeling CFSGOpposedSubgroupPeelingChain
variable {G : Type*} [Group G]

theorem peel_le_of_remainder_le (U V R S : Subgroup G) (w : G)
    (hRU : R≤U) (hBR : inversionPart U V w≤R) (hdis : Disjoint U V)
    (hfactor : ∀x∈U,∃p∈U,∃b∈inversionPart U V w,x=p*b ∧ w*p*w⁻¹∈U)
    (hw : w∈S) (hB : inversionPart U V w≤S) (hnext : remainderPart U R w≤S) : R≤S := by
  intro x hx
  obtain ⟨⟨r,b⟩,he⟩ := (peelProduct_bijective U V R w hRU hBR hdis hfactor).surjective ⟨x,hx⟩
  have hv := congrArg (fun z : R=>z.val) he
  change w⁻¹*r.val*w*b.val=x at hv
  have hm : w⁻¹*r.val*w*b.val∈S :=
    S.mul_mem (S.mul_mem (S.mul_mem (S.inv_mem hw) (hnext r.property)) hw) (hB b.property)
  exact hv ▸ hm

theorem positive_le_of_terminal_residual (U V S : Subgroup G) (w : ℕ→G)
    (hdis : Disjoint U V) (n : ℕ) :
    (∀j<n,w j∈S) →
    (∀j<n,inversionPart U V (w j)≤S) →
    (∀j<n,inversionPart U V (w j)≤residual U w j) →
    (∀j<n,∀x∈U,∃p∈U,∃b∈inversionPart U V (w j),x=p*b ∧ w j*p*(w j)⁻¹∈U) →
    residual U w n≤S → U≤S := by
  induction n with
  | zero=>
    intro _ _ _ _ hlast
    exact hlast
  | succ n ih=>
    intro hW hB hBR hfactor hlast
    have hn : n<n+1 := Nat.lt_succ_self n
    have hprev : residual U w n≤S :=
      peel_le_of_remainder_le U V (residual U w n) S (w n) (residual_le U w n)
        (hBR n hn) hdis (hfactor n hn) (hW n hn) (hB n hn) hlast
    exact ih (fun j hj=>hW j (Nat.lt_trans hj hn))
      (fun j hj=>hB j (Nat.lt_trans hj hn)) (fun j hj=>hBR j (Nat.lt_trans hj hn))
      (fun j hj=>hfactor j (Nat.lt_trans hj hn)) hprev

theorem positive_le_of_opposition (U V S : Subgroup G) (w : ℕ→G) (n : ℕ)
    (hdis : Disjoint U V) (hW : ∀j<n,w j∈S)
    (hB : ∀j<n,inversionPart U V (w j)≤S)
    (hBR : ∀j<n,inversionPart U V (w j)≤residual U w j)
    (hfactor : ∀j<n,∀x∈U,∃p∈U,∃b∈inversionPart U V (w j),x=p*b ∧ w j*p*(w j)⁻¹∈U)
    (hopp : U.map (MulAut.conj (wordPrefix w n)).toMonoidHom≤V) : U≤S := by
  apply positive_le_of_terminal_residual U V S w hdis n hW hB hBR hfactor
  rw [residual_eq_bot_of_opposition U V w n hdis hopp]
  exact bot_le

end SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupReversePeeling
