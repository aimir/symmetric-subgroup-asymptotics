import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWordMultiplication

/-! An actual order-q-squared middle subgroup of the pinned original
ReeF4 fixed group. Closure comes from the literal four-word multiplication
and inverse, while the fixed classification identifies its two-parameter
range. No whole-U or derived-central-quotient identification is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedSubgroup
open CFSG.Models.Chevalley CFSGReeFFourFieldParameters
open CFSGReeFFourMiddleFixedWords CFSGReeFFourMiddleFixedParameters
open CFSGReeFFourMiddleFixedClassification CFSGReeFFourMiddleWordMultiplication
open CFSGReeFFourFixedModelEquivalence

def middleFixedSubgroup (m : ℕ) : Subgroup (originalModelFixed m) where
  carrier := {g | ∃a b c d : Field m,middleWord m a b c d=g.val}
  one_mem' := ⟨0,0,0,0,middleWord_zero m⟩
  mul_mem' := by
    rintro x y ⟨a,b,c,d,hx⟩ ⟨e,f,s,t,hy⟩
    refine ⟨a+e,b+f,c+s+e*b,d+t+e^2*b,?_⟩
    change middleWord m (a+e) (b+f) (c+s+e*b) (d+t+e^2*b)=x.val*y.val
    rw [←middleWord_mul,hx,hy]
  inv_mem' := by
    rintro x ⟨a,b,c,d,hx⟩
    refine ⟨a,b,c+a*b,d+a^2*b,?_⟩
    change middleWord m a b (c+a*b) (d+a^2*b)=(x.val)⁻¹
    rw [←middleWord_inv,hx]

theorem middleFixedSubgroup_set (m : ℕ) :
    (middleFixedSubgroup m : Set (originalModelFixed m))=Set.range (fixedMiddleParameter m) := by
  apply Set.ext
  intro g
  change (∃a b c d : Field m,middleWord m a b c d=g.val) ↔
    ∃p : Field m×Field m,fixedMiddleParameter m p=g
  constructor
  · exact exists_fixedMiddleParameter_of_word m g
  · rintro ⟨p,rfl⟩
    exact ⟨p.1,alpha m p.1,p.2,alpha m p.2+p.1^2*alpha m p.1,rfl⟩

theorem middleFixedSubgroup_card (m : ℕ) :
    Nat.card (middleFixedSubgroup m)=(2^(2*m+1))^2 := by
  calc
    _=Nat.card (Set.range (fixedMiddleParameter m)) :=
      Nat.card_congr (Equiv.setCongr (middleFixedSubgroup_set m))
    _=_ := fixedMiddleParameter_range_card m

def originalMiddleFixedSubgroup (m : ℕ) :
    Subgroup (fixedSubgroup CartanMatrix.F₄ (Field m) CFSG.Models.reverseNode (originalExponent m)) :=
  (middleFixedSubgroup m).comap (originalFixedEquiv m).toMonoidHom

theorem originalMiddleFixedSubgroup_set (m : ℕ) :
    (originalMiddleFixedSubgroup m : Set (fixedSubgroup CartanMatrix.F₄ (Field m)
      CFSG.Models.reverseNode (originalExponent m)))=Set.range (originalFixedMiddleParameter m) := by
  apply Set.ext
  intro g
  change (∃a b c d : Field m,middleWord m a b c d=(originalFixedEquiv m g).val) ↔
    ∃p : Field m×Field m,originalFixedMiddleParameter m p=g
  constructor
  · intro hg
    obtain ⟨p,hp⟩ := exists_fixedMiddleParameter_of_word m (originalFixedEquiv m g) hg
    refine ⟨p,?_⟩
    apply (originalFixedEquiv m).injective
    change originalFixedEquiv m ((originalFixedEquiv m).symm (fixedMiddleParameter m p))=
      originalFixedEquiv m g
    rw [(originalFixedEquiv m).apply_symm_apply,hp]
  · rintro ⟨p,rfl⟩
    change originalFixedEquiv m ((originalFixedEquiv m).symm (fixedMiddleParameter m p))∈
      middleFixedSubgroup m
    rw [(originalFixedEquiv m).apply_symm_apply]
    exact ⟨p.1,alpha m p.1,p.2,alpha m p.2+p.1^2*alpha m p.1,rfl⟩

theorem originalMiddleFixedSubgroup_card (m : ℕ) :
    Nat.card (originalMiddleFixedSubgroup m)=(2^(2*m+1))^2 := by
  calc
    _=Nat.card (Set.range (originalFixedMiddleParameter m)) :=
      Nat.card_congr (Equiv.setCongr (originalMiddleFixedSubgroup_set m))
    _=_ := originalFixedMiddleParameter_range_card m

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedSubgroup
