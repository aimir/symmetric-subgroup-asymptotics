import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport

/-! Counting original epimorphisms using labels that determine their
literal kernels. Each kernel contributes exactly the original target
automorphism count. The label criterion is an explicit mathematical
premise; a centre dimension alone does not establish it. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {J Q : Type*} [Group J] [Group Q]

def epimorphismChangeTarget (f g : GroupEpimorphism J Q) (h : f.1.ker=g.1.ker) :
    Q≃*Q :=
  (QuotientGroup.liftEquiv f.1.ker f.2 rfl).symm.trans
    (QuotientGroup.liftEquiv f.1.ker g.2 h)

@[simp] theorem epimorphismChangeTarget_apply (f g : GroupEpimorphism J Q)
    (h : f.1.ker=g.1.ker) (x : J) : epimorphismChangeTarget f g h (f.1 x)=g.1 x := by
  change QuotientGroup.liftEquiv f.1.ker g.2 h
    ((QuotientGroup.liftEquiv f.1.ker f.2 rfl).symm (f.1 x))=g.1 x
  have hf : QuotientGroup.liftEquiv f.1.ker f.2 rfl
      (QuotientGroup.mk' f.1.ker x)=f.1 x := rfl
  rw [←hf,MulEquiv.symm_apply_apply]
  rfl

def groupEpimorphismKernelFibreEquiv (f : GroupEpimorphism J Q) :
    {g : GroupEpimorphism J Q // g.1.ker=f.1.ker}≃(Q≃*Q) where
  toFun g := epimorphismChangeTarget f g.1 g.2.symm
  invFun e := ⟨⟨e.toMonoidHom.comp f.1,e.surjective.comp f.2⟩,by
    ext x
    change e (f.1 x)=1 ↔ f.1 x=1
    exact e.map_eq_one_iff⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    exact epimorphismChangeTarget_apply f g.1 g.2.symm x
  right_inv e := by
    ext q
    obtain ⟨x,rfl⟩ := f.2 q
    exact epimorphismChangeTarget_apply _ _ _ x

theorem groupEpimorphism_kernel_fibre_card (f : GroupEpimorphism J Q) :
    Nat.card {g : GroupEpimorphism J Q // g.1.ker=f.1.ker}=Nat.card (Q≃*Q) :=
  Nat.card_congr (groupEpimorphismKernelFibreEquiv f)

/-- No faithful degree of a quotient is used: all maps have the same
complete original source J and the same literal target Q. -/
theorem groupEpimorphism_card_le_kernel_labels {L : Type*} [Finite L] [Finite Q]
    (label : GroupEpimorphism J Q→L)
    (hlabel : ∀ f g,label f=label g → f.1.ker=g.1.ker) :
    Nat.card (GroupEpimorphism J Q)≤Nat.card L*Nat.card (Q≃*Q) := by
  classical
  letI : Finite (Q≃*Q) := Finite.of_injective (fun e:Q≃*Q=>(e:Q→Q))
    DFunLike.coe_injective
  cases isEmpty_or_nonempty (GroupEpimorphism J Q) with
  | inl h => letI:=h; simp
  | inr h =>
    letI := h
    let chosen : L→GroupEpimorphism J Q := Function.invFun label
    have hc (f : GroupEpimorphism J Q) : label (chosen (label f))=label f :=
      Function.invFun_eq ⟨f,rfl⟩
    let encode : GroupEpimorphism J Q→L×(Q≃*Q) := fun f=>
      (label f,epimorphismChangeTarget (chosen (label f)) f (hlabel _ _ (hc f)))
    have hi : Function.Injective encode := by
      intro f g he
      have hl : label f=label g := congrArg Prod.fst he
      have ha := congrArg Prod.snd he
      apply Subtype.ext
      ext x
      have hx := DFunLike.congr_fun ha ((chosen (label f)).1 x)
      change epimorphismChangeTarget (chosen (label f)) f _ ((chosen (label f)).1 x)=
        epimorphismChangeTarget (chosen (label g)) g _ ((chosen (label f)).1 x) at hx
      rw [epimorphismChangeTarget_apply] at hx
      rw [hl,epimorphismChangeTarget_apply] at hx
      exact hx
    have hcard := Nat.card_le_card_of_injective encode hi
    rwa [Nat.card_prod] at hcard

end SymmetricSubgroupAsymptotics
