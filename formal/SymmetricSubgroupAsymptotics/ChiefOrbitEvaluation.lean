import SymmetricSubgroupAsymptotics.InducedTernaryEnvelope

/-! A local elementary evaluation on the original finite group produces
an actual induced quotient layer. Its kernel is the intersection of
the original translated evaluation kernels. No abelian source, split
extension, module embedding or chief filtration is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
section LocalChief
variable {p : ℕ} [Fact p.Prime]
variable {A N V : Type} [Group A] [Finite A] [Group N]
variable [AddCommGroup V] [Module (ZMod p) V]
variable (H : Subgroup A) (δ : A→*MulAut N)
variable (ρ : Representation (ZMod p) H V) (φ : N→*Multiplicative V)
variable (he : ∀ (h:H) (n:N),(φ (δ (h:A) n)).toAdd=ρ h (φ n).toAdd)

def localChiefCoinducedEvaluation : Additive N→+Representation.coindV H.subtype ρ where
  toFun n := ⟨fun a=>(φ (δ a n.toMul)).toAdd,by
    intro h a
    change (φ (δ ((h:A)*a) n.toMul)).toAdd=ρ h (φ (δ a n.toMul)).toAdd
    rw [map_mul,MulAut.mul_apply]
    exact he h (δ a n.toMul)⟩
  map_zero' := by
    apply Subtype.ext
    funext a
    change (φ (δ a 1)).toAdd=0
    simp
  map_add' n m := by
    apply Subtype.ext
    funext a
    change (φ (δ a (n.toMul*m.toMul))).toAdd=_
    simp only [map_mul]
    rfl

omit [Finite A] in
theorem localChiefCoinducedEvaluation_equivariant (a:A) (n:N) :
    localChiefCoinducedEvaluation H δ ρ φ he (Additive.ofMul (δ a n))=
      Representation.coind H.subtype ρ a
        (localChiefCoinducedEvaluation H δ ρ φ he (Additive.ofMul n)) := by
  apply Subtype.ext
  funext g
  change (φ (δ g (δ a n))).toAdd=(φ (δ (g*a) n)).toAdd
  rw [map_mul,MulAut.mul_apply]

def localChiefInducedEvaluation : Additive N→+Representation.IndV H.subtype ρ :=
  (inducedToCoinducedEquiv H ρ).symm.toLinearEquiv.toLinearMap.toAddMonoidHom.comp
    (localChiefCoinducedEvaluation H δ ρ φ he)

theorem localChiefInducedEvaluation_equivariant (a:A) (n:N) :
    localChiefInducedEvaluation H δ ρ φ he (Additive.ofMul (δ a n))=
      Representation.ind H.subtype ρ a
        (localChiefInducedEvaluation H δ ρ φ he (Additive.ofMul n)) := by
  change (inducedToCoinducedEquiv H ρ).symm
    (localChiefCoinducedEvaluation H δ ρ φ he (Additive.ofMul (δ a n)))=_
  rw [localChiefCoinducedEvaluation_equivariant]
  exact Representation.IntertwiningMap.isIntertwining _ _
    (inducedToCoinducedEquiv H ρ).symm.toIntertwiningMap a _

def localChiefInducedImage : Subrepresentation (Representation.ind H.subtype ρ) where
  toSubmodule := AddSubgroup.toZModSubmodule p
    (localChiefInducedEvaluation H δ ρ φ he).range
  apply_mem_toSubmodule a := by
    rintro _ ⟨n,rfl⟩
    exact ⟨Additive.ofMul (δ a n.toMul),localChiefInducedEvaluation_equivariant H δ ρ φ he a n.toMul⟩

def localChiefQuotientMap : N→*Multiplicative (localChiefInducedImage H δ ρ φ he).toSubmodule where
  toFun n := Multiplicative.ofAdd
    ⟨localChiefInducedEvaluation H δ ρ φ he (Additive.ofMul n),⟨Additive.ofMul n,rfl⟩⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_zero _
  map_mul' n m := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact map_add _ (Additive.ofMul n) (Additive.ofMul m)

theorem localChiefQuotientMap_surjective :
    Function.Surjective (localChiefQuotientMap H δ ρ φ he) := by
  intro v
  obtain ⟨n,hn⟩ := v.toAdd.2
  refine ⟨n.toMul,?_⟩
  apply Multiplicative.toAdd.injective
  exact Subtype.ext hn

theorem localChiefQuotientMap_equivariant (a:A) (n:N) :
    localChiefQuotientMap H δ ρ φ he (δ a n)=
      representationGroupAction (localChiefInducedImage H δ ρ φ he).toRepresentation a
        (localChiefQuotientMap H δ ρ φ he n) := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact localChiefInducedEvaluation_equivariant H δ ρ φ he a n

theorem localChiefInducedEvaluation_eq_zero_iff (n:N) :
    localChiefInducedEvaluation H δ ρ φ he (Additive.ofMul n)=0 ↔
      ∀a:A,φ (δ a n)=1 := by
  change (inducedToCoinducedEquiv H ρ).symm.toLinearEquiv
      (localChiefCoinducedEvaluation H δ ρ φ he (Additive.ofMul n))=0 ↔ _
  rw [←map_zero (inducedToCoinducedEquiv H ρ).symm.toLinearEquiv,
    (inducedToCoinducedEquiv H ρ).symm.toLinearEquiv.injective.eq_iff]
  constructor
  · intro h a
    apply Multiplicative.toAdd.injective
    exact congrArg (fun f : Representation.coindV H.subtype ρ=>f.1 a) h
  · intro h
    apply Subtype.ext
    funext a
    change (φ (δ a n)).toAdd=0
    rw [h a]
    rfl

theorem localChiefQuotientMap_kernel (n:N) :
    n∈(localChiefQuotientMap H δ ρ φ he).ker ↔ ∀a:A,φ (δ a n)=1 := by
  change localChiefQuotientMap H δ ρ φ he n=1 ↔ _
  rw [←localChiefInducedEvaluation_eq_zero_iff H δ ρ φ he]
  constructor
  · intro h
    exact congrArg (fun v : Multiplicative (localChiefInducedImage H δ ρ φ he).toSubmodule =>
      v.toAdd.1) h
  · intro h
    apply Multiplicative.toAdd.injective
    exact Subtype.ext h

/-- The actual extendible restriction image, before any enlargement. -/
def localChiefRetainedCharacters :=
  primeActionExtendibleCharacters p (localChiefQuotientMap H δ ρ φ he) δ
    (representationGroupAction (localChiefInducedImage H δ ρ φ he).toRepresentation)
    (localChiefQuotientMap_equivariant H δ ρ φ he)

theorem localChief_head_eq [Finite N] :
    Module.finrank (ZMod p) (primeActionCharacters p δ)=
      Module.finrank (ZMod p) (primeActionCharacters p
        (representationGroupAction (localChiefInducedImage H δ ρ φ he).toRepresentation))+
      Module.finrank (ZMod p) (localChiefRetainedCharacters H δ ρ φ he) := by
  letI : Finite (Multiplicative (localChiefInducedImage H δ ρ φ he).toSubmodule) :=
    Finite.of_surjective _ (localChiefQuotientMap_surjective H δ ρ φ he)
  exact primeActionCharacterRank_extension_eq p (localChiefQuotientMap H δ ρ φ he) δ
    (representationGroupAction (localChiefInducedImage H δ ρ φ he).toRepresentation)
    (localChiefQuotientMap_equivariant H δ ρ φ he)
    (localChiefQuotientMap_surjective H δ ρ φ he)

end LocalChief

/-- One genuine elementary local step of the block recurrence. The
kernel and retained restriction image are constructed from the original
local evaluation, while only its actual induced quotient is bounded. -/
theorem localChief_ternary_step
    (hTracey : TraceyPrimePowerModuleInput 3)
    {A N V : Type} [Group A] [Finite A] [Group N] [Finite N]
    [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (H : Subgroup A) (δ : A→*MulAut N)
    (ρ : Representation (ZMod 3) H V) (φ : N→*Multiplicative V)
    (he : ∀ (h:H) (n:N),(φ (δ (h:A) n)).toAdd=ρ h (φ n).toAdd) :
    (Module.finrank (ZMod 3) (primeActionCharacters 3 δ):ℝ)≤
      (Module.finrank (ZMod 3) V:ℝ)*traceyTernaryEnvelope H.index+
        (Module.finrank (ZMod 3) (localChiefRetainedCharacters H δ ρ φ he):ℝ) := by
  have hnat := localChief_head_eq H δ ρ φ he
  have hreal := congrArg (Nat.cast : ℕ→ℝ) hnat
  simp only [Nat.cast_add] at hreal
  have hb := inducedTernary_head_le_envelope hTracey H ρ
    (localChiefInducedImage H δ ρ φ he)
  exact hreal.trans_le (add_le_add hb le_rfl)

end SymmetricSubgroupAsymptotics
