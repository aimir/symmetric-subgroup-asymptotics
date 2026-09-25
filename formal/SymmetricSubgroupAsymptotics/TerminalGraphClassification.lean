import SymmetricSubgroupAsymptotics.BinaryAbelianization
import SymmetricSubgroupAsymptotics.TerminalRecords
import Mathlib.GroupTheory.Goursat

/-!
# Actual terminal images as quotient graphs

Every subgroup of V×T that projects onto the whole exterior is uniquely the
graph modulo its actual vertical kernel. The quotient map is an actual
homomorphism on T and, when finite, factors through its complete elementary
binary quotient. No splitting condition on later central lifts is assumed.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {V T : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Group T]

abbrev TerminalFullImages :=
  {Y : Subgroup (Multiplicative V × T) // Y.map (MonoidHom.snd (Multiplicative V) T) = ⊤}

/-- The literal vertical kernel, viewed as a binary subspace. -/
def terminalVerticalSpace (Y : Subgroup (Multiplicative V × T)) : Submodule (ZMod 2) V :=
  (AddSubgroup.toZModSubmodule 2) (AddSubgroup.toSubgroup.symm Y.goursatFst)

@[simp] theorem mem_terminalVerticalSpace (Y : Subgroup (Multiplicative V × T)) (v : V) :
    v ∈ terminalVerticalSpace Y ↔ (Multiplicative.ofAdd v,1) ∈ Y := by
  change Multiplicative.ofAdd v ∈ Y.goursatFst ↔ _
  exact Subgroup.mem_goursatFst

private def terminalImageProjection (Y : TerminalFullImages (V := V) (T := T)) : Y.1 →* T :=
  (MonoidHom.snd (Multiplicative V) T).comp Y.1.subtype

omit [Module (ZMod 2) V] in
private theorem terminalImageProjection_surjective (Y : TerminalFullImages (V := V) (T := T)) :
    Function.Surjective (terminalImageProjection Y) := by
  intro t
  have ht : t ∈ Y.1.map (MonoidHom.snd (Multiplicative V) T) := by rw [Y.2]; trivial
  obtain ⟨x,hx,ht⟩ := Subgroup.mem_map.mp ht
  exact ⟨⟨x,hx⟩,ht⟩

private def terminalImageQuotient (Y : TerminalFullImages (V := V) (T := T)) :
    Y.1 →* Multiplicative (V ⧸ terminalVerticalSpace Y.1) :=
  (AddMonoidHom.toMultiplicative (terminalVerticalSpace Y.1).mkQ.toAddMonoidHom).comp
    ((MonoidHom.fst (Multiplicative V) T).comp Y.1.subtype)

private theorem terminalImageProjection_ker_le (Y : TerminalFullImages (V := V) (T := T)) :
    (terminalImageProjection Y).ker ≤ (terminalImageQuotient Y).ker := by
  intro x hx
  change x.1.2 = 1 at hx
  change (terminalVerticalSpace Y.1).mkQ x.1.1.toAdd = 0
  change x.1.1.toAdd ∈ (terminalVerticalSpace Y.1).mkQ.ker
  rw [(terminalVerticalSpace Y.1).ker_mkQ,mem_terminalVerticalSpace]
  simpa only [← hx] using x.2

/-- The original quotient graph character, obtained by descent from the
actual subgroup. -/
def terminalGraphCharacter (Y : TerminalFullImages (V := V) (T := T)) :
    T →* Multiplicative (V ⧸ terminalVerticalSpace Y.1) :=
  (terminalImageProjection Y).liftOfSurjective (terminalImageProjection_surjective Y)
    ⟨terminalImageQuotient Y,terminalImageProjection_ker_le Y⟩

@[simp] theorem terminalGraphCharacter_apply (Y : TerminalFullImages (V := V) (T := T))
    (x : Y.1) : terminalGraphCharacter Y x.1.2 =
      Multiplicative.ofAdd ((terminalVerticalSpace Y.1).mkQ x.1.1.toAdd) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

/-- The literal pullback graph inside the complete original product V×T. -/
def terminalQuotientGraph (U : Submodule (ZMod 2) V)
    (f : T →* Multiplicative (V ⧸ U)) : Subgroup (Multiplicative V × T) :=
  f.graph.comap ((MonoidHom.snd (Multiplicative V) T).prod
    ((AddMonoidHom.toMultiplicative U.mkQ.toAddMonoidHom).comp (MonoidHom.fst (Multiplicative V) T)))

@[simp] theorem mem_terminalQuotientGraph (U : Submodule (ZMod 2) V)
    (f : T →* Multiplicative (V ⧸ U)) (x : Multiplicative V × T) :
    x ∈ terminalQuotientGraph U f ↔ f x.2 = Multiplicative.ofAdd (U.mkQ x.1.toAdd) := Iff.rfl

theorem terminalQuotientGraph_full (U : Submodule (ZMod 2) V)
    (f : T →* Multiplicative (V ⧸ U)) :
    (terminalQuotientGraph U f).map (MonoidHom.snd (Multiplicative V) T) = ⊤ := by
  apply top_unique
  intro t ht
  obtain ⟨v,hv⟩ := U.mkQ_surjective (f t).toAdd
  exact Subgroup.mem_map.mpr ⟨(Multiplicative.ofAdd v,t),by
    change f t = Multiplicative.ofAdd (U.mkQ v)
    rw [hv]; rfl,rfl⟩

@[simp] theorem terminalQuotientGraph_vertical (U : Submodule (ZMod 2) V)
    (f : T →* Multiplicative (V ⧸ U)) :
    terminalVerticalSpace (terminalQuotientGraph U f) = U := by
  ext v
  rw [mem_terminalVerticalSpace,mem_terminalQuotientGraph,map_one]
  change (0 : V ⧸ U) = U.mkQ v ↔ v ∈ U
  rw [eq_comm,← LinearMap.mem_ker,U.ker_mkQ]

/-- Every actual image is recovered from its vertical kernel and quotient
character, even when its projection inside V is proper. -/
theorem terminalGraphCharacter_recovers (Y : TerminalFullImages (V := V) (T := T)) :
    terminalQuotientGraph (terminalVerticalSpace Y.1) (terminalGraphCharacter Y) = Y.1 := by
  ext x
  rw [mem_terminalQuotientGraph]
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := terminalImageProjection_surjective Y x.2
    change y.1.2 = x.2 at hy
    have hx' := congrArg Multiplicative.toAdd hx
    change (terminalGraphCharacter Y x.2).toAdd = (terminalVerticalSpace Y.1).mkQ x.1.toAdd at hx'
    have hq : (terminalVerticalSpace Y.1).mkQ (x.1.toAdd-y.1.1.toAdd) = 0 := by
      rw [map_sub,← hx',← hy,terminalGraphCharacter_apply]
      exact sub_self _
    have hu : x.1.toAdd-y.1.1.toAdd ∈ terminalVerticalSpace Y.1 := by
      exact (terminalVerticalSpace Y.1).ker_mkQ ▸ hq
    have hv := (mem_terminalVerticalSpace Y.1 _).mp hu
    have hmul := Y.1.mul_mem hv y.2
    have he : (Multiplicative.ofAdd (x.1.toAdd-y.1.1.toAdd),(1 : T))*y.1 = x := by
      apply Prod.ext
      · change Multiplicative.ofAdd (x.1.toAdd-y.1.1.toAdd+y.1.1.toAdd) = x.1
        simp
      · simpa using hy
    simpa only [he] using hmul
  · intro hx
    exact terminalGraphCharacter_apply Y ⟨x,hx⟩

private def terminalGraphParameterMap :
    (Σ U : Submodule (ZMod 2) V, T →* Multiplicative (V ⧸ U)) →
      TerminalFullImages (V := V) (T := T) :=
  fun p ↦ ⟨terminalQuotientGraph p.1 p.2,terminalQuotientGraph_full p.1 p.2⟩

private theorem terminalGraphParameterMap_injective :
    Function.Injective (terminalGraphParameterMap (V := V) (T := T)) := by
  rintro ⟨U,f⟩ ⟨W,g⟩ h
  have he : terminalQuotientGraph U f = terminalQuotientGraph W g := congrArg Subtype.val h
  have hU := congrArg terminalVerticalSpace he
  simp only [terminalQuotientGraph_vertical] at hU
  subst W
  have hf : f = g := by
    apply MonoidHom.ext
    intro t
    obtain ⟨v,hv⟩ := U.mkQ_surjective (f t).toAdd
    have hm : (Multiplicative.ofAdd v,t) ∈ terminalQuotientGraph U f := by
      change f t = Multiplicative.ofAdd (U.mkQ v)
      rw [hv]; rfl
    rw [he,mem_terminalQuotientGraph] at hm
    change g t = Multiplicative.ofAdd (U.mkQ v) at hm
    rw [hv] at hm
    exact hm.symm
  subst g
  rfl

private theorem terminalGraphParameterMap_surjective :
    Function.Surjective (terminalGraphParameterMap (V := V) (T := T)) := by
  intro Y
  exact ⟨⟨terminalVerticalSpace Y.1,terminalGraphCharacter Y⟩,
    Subtype.ext (terminalGraphCharacter_recovers Y)⟩

/-- Exact classification of all actual exterior-full images. -/
def terminalGraphClassification :
    TerminalFullImages (V := V) (T := T) ≃
      (Σ U : Submodule (ZMod 2) V, T →* Multiplicative (V ⧸ U)) :=
  (Equiv.ofBijective terminalGraphParameterMap
    ⟨terminalGraphParameterMap_injective,terminalGraphParameterMap_surjective⟩).symm

/-- The same complete image classification in additive character notation. -/
def terminalGraphAdditiveClassification :
    TerminalFullImages (V := V) (T := T) ≃
      (Σ U : Submodule (ZMod 2) V, Additive T →+ V ⧸ U) :=
  terminalGraphClassification.trans (Equiv.sigmaCongrRight fun _ ↦
    AddMonoidHom.toMultiplicativeRight.symm)

/-- Every actual terminal image has one quotient graph map on the complete
canonical elementary binary quotient of the exterior. -/
def terminalGraphLinearClassification [Finite T] [Finite V] :
    TerminalFullImages (V := V) (T := T) ≃
      (Σ U : Submodule (ZMod 2) V, BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U) :=
  terminalGraphClassification.trans (Equiv.sigmaCongrRight fun U ↦ by
    letI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
    exact binaryAbelianizationGroupHomEquiv T)

/-- A linear graph on the complete binary quotient pulled back to the
original complete exterior. -/
def terminalLinearQuotientGraph (U : Submodule (ZMod 2) V)
    (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U) : Subgroup (Multiplicative V × T) :=
  terminalQuotientGraph U (AddMonoidHom.toMultiplicativeRight
    (f.toAddMonoidHom.comp (binaryAbelianizationMap T)))

@[simp] theorem mem_terminalLinearQuotientGraph (U : Submodule (ZMod 2) V)
    (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U) (x : Multiplicative V × T) :
    x ∈ terminalLinearQuotientGraph U f ↔
      f (binaryAbelianizationMap T (Additive.ofMul x.2)) = U.mkQ x.1.toAdd := Iff.rfl

/-- The inverse classification constructs this literal pullback subgroup. -/
theorem terminalGraphLinearClassification_symm [Finite T] [Finite V]
    (U : Submodule (ZMod 2) V) (f : BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U) :
    ((terminalGraphLinearClassification (V := V) (T := T)).symm ⟨U,f⟩).1 =
      terminalLinearQuotientGraph U f := rfl

/-- Arbitrary future survival predicates are retained before counting
records or applying any weight on the actual image. -/
def terminalGraphRestrictedClassification [Finite T] [Finite V]
    (P : TerminalFullImages (V := V) (T := T) → Prop) :
    {Y : TerminalFullImages (V := V) (T := T) // P Y} ≃
      {p : (Σ U : Submodule (ZMod 2) V, BinaryAbelianization T →ₗ[ZMod 2] V ⧸ U) //
        P ((terminalGraphLinearClassification (V := V) (T := T)).symm p)} :=
  (terminalGraphLinearClassification (V := V) (T := T)).subtypeEquiv
    (fun Y ↦ by rw [Equiv.symm_apply_apply])

end SymmetricSubgroupAsymptotics
