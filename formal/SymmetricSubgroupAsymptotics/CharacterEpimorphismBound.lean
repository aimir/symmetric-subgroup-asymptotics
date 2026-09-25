import SymmetricSubgroupAsymptotics.IrreducibleCharacterLabels

/-! The character-count envelope from an actual faithful tuple of
irreducible target representations. The full original source J and its
conjugacy classes are retained throughout. Existence of the target tuple
and a numerical class-count estimate are separate inputs to applications. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics

theorem representation_kernel_le_of_equiv {k G V W : Type*}
    [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.ker≤σ.ker := by
  intro g hg
  change σ g=1
  ext w
  obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
  change σ g (e v)=e v
  have he := Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v
  change e (ρ g v)=σ g (e v) at he
  rw [←he]
  rw [show ρ g=1 from hg]
  rfl

theorem representation_kernel_eq_of_equiv {k G V W : Type*}
    [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W} (e : ρ.Equiv σ) :
    ρ.ker=σ.ker :=
  le_antisymm (representation_kernel_le_of_equiv e) (representation_kernel_le_of_equiv e.symm)

variable {k J Q V : Type*} [Field k] [IsAlgClosed k] [Group J] [Group Q]
    [Finite J] [Finite Q] [Invertible (Nat.card J:k)]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]

def epimorphismCharacterLabels (ρ : Representation k Q V) : Type _ :=
  Set.range (fun f : GroupEpimorphism J Q=>Representation.character (ρ.comp f.1))

instance epimorphismCharacterLabels_finite (ρ : Representation k Q V) :
    Finite (epimorphismCharacterLabels (J := J) ρ) := by
  letI : Finite (GroupEpimorphism J Q) := Finite.of_injective
    (fun f : GroupEpimorphism J Q=>(f.1:J→Q))
    (fun _ _ h=>Subtype.ext (DFunLike.coe_injective h))
  unfold epimorphismCharacterLabels
  infer_instance

theorem epimorphismCharacterLabels_card (ρ : Representation k Q V)
    [Representation.IsIrreducible ρ] :
    Nat.card (epimorphismCharacterLabels (J := J) ρ)≤Nat.card (ConjClasses J) := by
  classical
  letI := Fintype.ofFinite J
  let L := epimorphismCharacterLabels (J := J) ρ
  letI := Fintype.ofFinite L
  let β (x : L) : GroupEpimorphism J Q := x.property.choose
  let τ (x : L) : Representation k J V := ρ.comp (β x).1
  letI (x : L) : Representation.IsIrreducible (τ x) :=
    representation_irreducible_comp ρ (β x).1 (β x).2
  have hχ (x : L) : (τ x).character=x.val := x.property.choose_spec
  have hi : Function.Injective (fun x:L=>(τ x).character) := by
    intro x y h
    apply Subtype.ext
    exact (hχ x).symm.trans (h.trans (hχ y))
  simpa only [Nat.card_eq_fintype_card] using
    irreducible_character_family_card_le (fun _:L=>V) τ hi

/-- A faithful tuple of z actual irreducibles gives the original
|Aut Q| k(J)^z envelope, with no independence assumption on the labels. -/
theorem groupEpimorphism_card_le_faithful_characters
    {ι : Type*} [Fintype ι] (W : ι→Type*) [∀i,AddCommGroup (W i)]
    [∀i,Module k (W i)] [∀i,FiniteDimensional k (W i)]
    (ρ : ∀i,Representation k Q (W i)) [∀i,Representation.IsIrreducible (ρ i)]
    (hfaithful : ∀q:Q,(∀i,ρ i q=1)→q=1) :
    Nat.card (GroupEpimorphism J Q)≤
      Nat.card (Q≃*Q)*Nat.card (ConjClasses J)^Fintype.card ι := by
  classical
  letI := Fintype.ofFinite J
  let label : GroupEpimorphism J Q→(∀i,epimorphismCharacterLabels (J := J) (ρ i)) :=
    fun f i=>⟨Representation.character ((ρ i).comp f.1),⟨f,rfl⟩⟩
  have hk : ∀f g,label f=label g→f.1.ker=g.1.ker := by
    intro f g he
    have hrep (i : ι) : ((ρ i).comp f.1).ker=((ρ i).comp g.1).ker := by
      letI : Representation.IsIrreducible ((ρ i).comp f.1) :=
        representation_irreducible_comp (ρ i) f.1 f.2
      letI : Representation.IsIrreducible ((ρ i).comp g.1) :=
        representation_irreducible_comp (ρ i) g.1 g.2
      obtain ⟨e⟩ := irreducible_equiv_of_character_eq ((ρ i).comp f.1) ((ρ i).comp g.1)
        (congrArg Subtype.val (congrFun he i))
      exact representation_kernel_eq_of_equiv e
    ext x
    change f.1 x=1 ↔ g.1 x=1
    constructor
    · intro hx
      apply hfaithful
      intro i
      have hm : x∈((ρ i).comp f.1).ker := by change ρ i (f.1 x)=1; rw [hx,map_one]
      change x∈((ρ i).comp g.1).ker
      rwa [hrep i] at hm
    · intro hx
      apply hfaithful
      intro i
      have hm : x∈((ρ i).comp g.1).ker := by change ρ i (g.1 x)=1; rw [hx,map_one]
      change x∈((ρ i).comp f.1).ker
      rwa [←hrep i] at hm
  have h := groupEpimorphism_card_le_kernel_labels label hk
  have hc : Nat.card (∀i,epimorphismCharacterLabels (J := J) (ρ i))≤
      Nat.card (ConjClasses J)^Fintype.card ι := by
    rw [Nat.card_pi]
    calc
      _≤∏_i:ι,Nat.card (ConjClasses J) :=
        Finset.prod_le_prod (fun _ _=>Nat.zero_le _)
          (fun i _=>epimorphismCharacterLabels_card (J := J) (ρ i))
      _=_ := by simp
  exact h.trans ((Nat.mul_le_mul_right _ hc).trans_eq (Nat.mul_comm _ _))

end SymmetricSubgroupAsymptotics
