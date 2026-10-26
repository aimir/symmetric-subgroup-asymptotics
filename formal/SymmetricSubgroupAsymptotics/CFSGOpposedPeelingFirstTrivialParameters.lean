import SymmetricSubgroupAsymptotics.CFSGOpposedPeelingOrderedParameters

/-! A genuine first-remainder element has first inversion parameter one
in the literal ordered peel cover. Only the already proved peel-product
injectivity is used; later factors are not asserted to belong to any
additional normal subgroup containing the original element. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOpposedPeelingFirstTrivialParameters
open CFSGOpposedSubgroupPeeling CFSGOpposedSubgroupPeelingChain
open CFSGOpposedPeelingOrderedParameters
variable {G : Type*} [Group G]

private theorem first_peel_second_one (U V : Subgroup G) (w : G)
    (hBR : inversionPart U V w≤U) (hdis : Disjoint U V)
    (x : G) (hx : x∈U) (hc : w*x*w⁻¹∈U)
    (p : remainderPart U U w × inversionPart U V w)
    (hp : (peelProduct U V U w hBR p).val=x) : p.2.val=1 := by
  let q : remainderPart U U w × inversionPart U V w :=
    (⟨w*x*w⁻¹,⟨hc,⟨x,hx,rfl⟩⟩⟩,1)
  have hq : (peelProduct U V U w hBR q).val=x := by
    change w⁻¹*(w*x*w⁻¹)*w*1=x
    group
  have he : p=q := peelProduct_injective U V U w hBR hdis
    (Subtype.ext (hp.trans hq.symm))
  exact congrArg (fun t : remainderPart U U w × inversionPart U V w => t.2.val) he

theorem exists_residual_parameters_first_one
    (U V : Subgroup G) (w : ℕ→G) (n : ℕ)
    (hdis : Disjoint U V)
    (hBR : ∀j<n,inversionPart U V (w j)≤residual U w j)
    (hfactor : ∀j<n,∀x∈U,∃p∈U,∃b∈inversionPart U V (w j),
      x=p*b ∧ w j*p*(w j)⁻¹∈U)
    (x : G) (hx : x∈U) (hc : w 0*x*(w 0)⁻¹∈U) :
    ∃r∈residual U w n,∃b : Fin n→G,
      (∀j,b j∈inversionPart U V (w j.val)) ∧
      x=((wordPrefix w n)⁻¹*r*wordPrefix w n)*orderedProduct w n b ∧
      (∀h : 0<n,b ⟨0,h⟩=1) := by
  induction n with
  | zero =>
    refine ⟨x,hx,Fin.elim0,?_,?_,?_⟩
    · intro j
      exact Fin.elim0 j
    · simp only [wordPrefix,orderedProduct,inv_one,one_mul,mul_one]
    · intro h
      omega
  | succ n ih =>
    have hn : n<n+1 := Nat.lt_succ_self n
    obtain ⟨r,hr,b,hb,he,hfirst⟩ := ih
      (fun j hj => hBR j (Nat.lt_trans hj hn))
      (fun j hj => hfactor j (Nat.lt_trans hj hn))
    obtain ⟨p,hp⟩ := (peelProduct_bijective U V (residual U w n) (w n)
      (residual_le U w n) (hBR n hn) hdis (hfactor n hn)).surjective ⟨r,hr⟩
    have hrow : (w n)⁻¹*p.1.val*w n*p.2.val=r :=
      congrArg (fun z : residual U w n => z.val) hp
    refine ⟨p.1.val,p.1.property,Fin.snoc b p.2.val,?_,?_,?_⟩
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.snoc_last,Fin.val_last] using p.2.property
      · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hb i
    · rw [he,←hrow]
      simp only [wordPrefix,orderedProduct,Fin.snoc_last,Fin.snoc_castSucc]
      group
    · intro h
      cases n with
      | zero =>
        have hrx : r=x := by
          simpa only [wordPrefix,orderedProduct,inv_one,one_mul,mul_one] using he.symm
        have hpx : (peelProduct U V U (w 0) (hBR 0 hn) p).val=x :=
          (congrArg (fun z : U => z.val) hp).trans hrx
        exact first_peel_second_one U V (w 0) (hBR 0 hn) hdis x hx hc p hpx
      | succ n =>
        have hz : (⟨0,h⟩ : Fin (n+1+1))=(⟨0,by omega⟩ : Fin (n+1)).castSucc := rfl
        rw [hz,Fin.snoc_castSucc]
        exact hfirst (by omega)

theorem exists_parameters_first_one_of_opposition
    (U V : Subgroup G) (w : ℕ→G) (n : ℕ)
    (hdis : Disjoint U V)
    (hBR : ∀j<n,inversionPart U V (w j)≤residual U w j)
    (hfactor : ∀j<n,∀x∈U,∃p∈U,∃b∈inversionPart U V (w j),
      x=p*b ∧ w j*p*(w j)⁻¹∈U)
    (hopp : U.map (MulAut.conj (wordPrefix w n)).toMonoidHom≤V)
    (x : G) (hx : x∈U) (hc : w 0*x*(w 0)⁻¹∈U) :
    ∃b : Fin n→G,(∀j,b j∈inversionPart U V (w j.val)) ∧
      x=orderedProduct w n b ∧ (∀h : 0<n,b ⟨0,h⟩=1) := by
  obtain ⟨r,hr,b,hb,he,hfirst⟩ :=
    exists_residual_parameters_first_one U V w n hdis hBR hfactor x hx hc
  have hr1 : r=1 := by
    rw [residual_eq_bot_of_opposition U V w n hdis hopp] at hr
    exact hr
  refine ⟨b,hb,?_,hfirst⟩
  simpa only [hr1,mul_one,inv_mul_cancel,one_mul] using he

end SymmetricSubgroupAsymptotics.CFSGOpposedPeelingFirstTrivialParameters
