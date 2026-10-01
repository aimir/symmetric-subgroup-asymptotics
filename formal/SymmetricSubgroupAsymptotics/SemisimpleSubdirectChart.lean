import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre
import SymmetricSubgroupAsymptotics.PerfectSubdirect

/-!
# Semisimple charts for full subdirect products

A full subdirect product of finitely many nonabelian simple groups is itself
a direct product of nonabelian simple groups.  This file proves the statement
constructively in the exact form needed by `SemisimpleNormalChart`.

The induction retains every proper diagonal correlation.  After projecting
to the first `n` coordinates, the image of that kernel in the last simple
factor is normal.  If it is trivial, the last coordinate is already
determined by the preceding ones.  If it is full, the last factor splits
off.  Thus no choice of diagonal strips or census of isomorphism types is
required.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- An abstract finite direct-product presentation by centerless simple
groups. -/
structure SemisimpleGroupChart (G : Type*) [Group G] where
  ι : Type
  [fintype : Fintype ι]
  factor : ι → Type
  [group : ∀ i, Group (factor i)]
  [finite : ∀ i, Finite (factor i)]
  simple : ∀ i, IsSimpleGroup (factor i)
  centerless : ∀ i, IsCenterless (factor i)
  equiv : G ≃* ((i : ι) → factor i)

attribute [instance] SemisimpleGroupChart.fintype SemisimpleGroupChart.group
  SemisimpleGroupChart.finite

namespace SemisimpleGroupChart

/-- Regard an abstract chart on a subgroup as the literal normal chart used
by the counting theorem. -/
def toNormalChart {U : Type*} [Group U] (E : Subgroup U)
    (C : SemisimpleGroupChart E) : SemisimpleNormalChart E where
  ι := C.ι
  factor := C.factor
  simple := C.simple
  centerless := C.centerless
  equiv := C.equiv

end SemisimpleGroupChart

/-- Scott's subdirect-product theorem in chart form.  The maps are the
literal coordinate maps; surjectivity and joint injectivity are the only
structural hypotheses. -/
theorem semisimpleGroupChart_of_subdirect_fin :
    ∀ (n : ℕ) (S : Fin n → Type)
      [∀ i, Group (S i)] [∀ i, Finite (S i)]
      [∀ i, IsSimpleGroup (S i)] (hcenterless : ∀ i, IsCenterless (S i))
      (G : Type) [Group G] (f : ∀ i, G →* S i),
      (∀ i, Function.Surjective (f i)) →
      Function.Injective (fun x i ↦ f i x) →
      Nonempty (SemisimpleGroupChart G) := by
  intro n
  induction n with
  | zero =>
      intro S _ _ _ hcenterless G _ f _ hi
      let F : G →* ((i : Fin 0) → S i) := Pi.monoidHom f
      have hF : Function.Bijective F := ⟨hi, by
        intro y
        exact ⟨1, Subsingleton.elim _ _⟩⟩
      exact ⟨{
        ι := Fin 0
        factor := S
        simple := fun i ↦ Fin.elim0 i
        centerless := hcenterless
        equiv := MulEquiv.ofBijective F hF }⟩
  | succ n ih =>
      intro S _ _ _ hcenterless G _ f hs hi
      let d : G →* ((i : Fin n) → S i.succ) :=
        Pi.monoidHom (fun i ↦ f i.succ)
      let A : Subgroup ((i : Fin n) → S i.succ) := d.range
      let p : G →* A := d.rangeRestrict
      let g : G →* S 0 := f 0
      let af (i : Fin n) : A →* S i.succ :=
        (Pi.evalMonoidHom (fun j : Fin n ↦ S j.succ) i).comp A.subtype
      have haf (i : Fin n) : Function.Surjective (af i) := by
        intro y
        obtain ⟨x, hx⟩ := hs i.succ y
        exact ⟨p x, hx⟩
      have ha_inj : Function.Injective (fun x i ↦ af i x) := by
        intro x y hxy
        apply Subtype.ext
        funext i
        exact congrFun hxy i
      obtain ⟨C⟩ := ih (fun i ↦ S i.succ)
        (fun i ↦ hcenterless i.succ) A af haf ha_inj
      let K : Subgroup (S 0) := p.ker.map g
      letI : K.Normal := Subgroup.Normal.map inferInstance g (hs 0)
      rcases Subgroup.Normal.eq_bot_or_eq_top (H := K) inferInstance with hK | hK
      · have hker : p.ker = ⊥ := by
          apply le_antisymm
          · intro x hx
            have hg_mem : g x ∈ K := ⟨x, hx, rfl⟩
            have hg : g x = 1 := by
              rw [hK, Subgroup.mem_bot] at hg_mem
              exact hg_mem
            apply Subgroup.mem_bot.mpr
            apply hi
            funext i
            refine Fin.cases ?_ (fun j ↦ ?_) i
            · simpa only [map_one] using hg
            · have hd : d x = 1 := congrArg Subtype.val hx
              simpa only [map_one] using congrFun hd j
          · exact bot_le
        have hp : Function.Bijective p :=
          ⟨(MonoidHom.ker_eq_bot_iff p).mp hker, d.rangeRestrict_surjective⟩
        let eGA : G ≃* A := MulEquiv.ofBijective p hp
        exact ⟨{
          ι := C.ι
          factor := C.factor
          simple := C.simple
          centerless := C.centerless
          equiv := eGA.trans C.equiv }⟩
      · let pg : G →* A × S 0 := p.prod g
        have hpg_inj : Function.Injective pg := by
          intro x y hxy
          apply hi
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · exact congrArg Prod.snd hxy
          · have hp_xy : p x = p y := congrArg Prod.fst hxy
            exact congrFun (congrArg Subtype.val hp_xy) j
        have hpg_surj : Function.Surjective pg := by
          rintro ⟨a, s⟩
          obtain ⟨x, hx⟩ := d.rangeRestrict_surjective a
          have htarget : (g x)⁻¹ * s ∈ K := by
            rw [hK]
            exact Subgroup.mem_top _
          obtain ⟨k, hk, hgk⟩ := htarget
          have hpk : p k = 1 := MonoidHom.mem_ker.mp hk
          refine ⟨x * k, ?_⟩
          apply Prod.ext
          · change p (x * k) = a
            rw [MonoidHom.map_mul, hx, hpk, mul_one]
          · change g (x * k) = s
            rw [MonoidHom.map_mul, hgk, mul_inv_cancel_left]
        let ePair : G ≃* A × S 0 :=
          MulEquiv.ofBijective pg ⟨hpg_inj, hpg_surj⟩
        let T : Option C.ι → Type
          | none => S 0
          | some i => C.factor i
        letI (j : Option C.ι) : Group (T j) := by
          cases j with
          | none => exact inferInstanceAs (Group (S 0))
          | some i => exact inferInstanceAs (Group (C.factor i))
        letI (j : Option C.ι) : Finite (T j) := by
          cases j with
          | none => exact inferInstanceAs (Finite (S 0))
          | some i => exact inferInstanceAs (Finite (C.factor i))
        let eProd : A × S 0 ≃* ((j : Option C.ι) → T j) := {
          toFun := fun x j ↦ match j with
            | none => x.2
            | some i => C.equiv x.1 i
          invFun := fun z ↦ ⟨C.equiv.symm (fun i ↦ z (some i)), z none⟩
          left_inv := by
            intro x
            apply Prod.ext
            · exact C.equiv.symm_apply_apply x.1
            · exact rfl
          right_inv := by
            intro z
            funext j
            cases j with
            | none => exact rfl
            | some i => exact congrFun (C.equiv.apply_symm_apply _) i
          map_mul' := by
            intro x y
            funext j
            cases j with
            | none => exact rfl
            | some i =>
                exact congrFun (C.equiv.map_mul x.1 y.1) i }
        let e : G ≃* ((j : Option C.ι) → T j) := ePair.trans eProd
        exact ⟨{
          ι := Option C.ι
          factor := T
          simple := fun j ↦ by
            cases j with
            | none => exact inferInstanceAs (IsSimpleGroup (S 0))
            | some i => exact C.simple i
          centerless := fun j ↦ by
            cases j with
            | none => exact hcenterless 0
            | some i => exact C.centerless i
          equiv := e }⟩

/-- Arbitrary finite coordinate sets, retaining the literal coordinate
maps. -/
theorem semisimpleGroupChart_of_subdirect
    {I : Type} [Fintype I] (S : I → Type)
    [∀ i, Group (S i)] [∀ i, Finite (S i)]
    [∀ i, IsSimpleGroup (S i)] (hcenterless : ∀ i, IsCenterless (S i))
    (G : Type) [Group G] (f : ∀ i, G →* S i)
    (hs : ∀ i, Function.Surjective (f i))
    (hi : Function.Injective (fun x i ↦ f i x)) :
    Nonempty (SemisimpleGroupChart G) := by
  let e := Fintype.equivFin I
  exact semisimpleGroupChart_of_subdirect_fin (Fintype.card I)
    (fun j ↦ S (e.symm j)) (fun j ↦ hcenterless (e.symm j)) G
    (fun j ↦ f (e.symm j)) (fun j ↦ hs (e.symm j)) (by
      intro x y hxy
      apply hi
      funext i
      obtain ⟨j, rfl⟩ := e.symm.surjective i
      exact congrFun hxy j)

namespace SemisimpleNormalChart

variable {R : Type} [Group R] {L : Subgroup R}

/-- One literal simple coordinate of a map into a charted semisimple
group. -/
def coordinate {G I : Type} [Group G] (C : SemisimpleNormalChart L)
    (f : I → G →* L) (i : I) (j : C.ι) : G →* C.factor j :=
  (Pi.evalMonoidHom C.factor j).comp (C.equiv.toMonoidHom.comp (f i))

/-- If every simple-coordinate image is normal, its image is either zero or
the complete simple factor.  Removing the zero coordinates and applying the
subdirect theorem gives a literal semisimple chart. -/
def chartOfNormalCoordinateMaps
    {G I : Type} [Group G] [Fintype I]
    (C : SemisimpleNormalChart L) (f : I → G →* L)
    (hn : ∀ i j, (C.coordinate f i j).range.Normal)
    (hi : Function.Injective (fun x i ↦ f i x)) :
    SemisimpleGroupChart G := by
  classical
  let Full := {p : I × C.ι // Function.Surjective (C.coordinate f p.1 p.2)}
  let S : Full → Type := fun p ↦ C.factor p.1.2
  letI (p : Full) : IsSimpleGroup (S p) := C.simple p.1.2
  let coord (p : Full) : G →* S p := C.coordinate f p.1.1 p.1.2
  have hzero_or_full (i : I) (j : C.ι) :
      (C.coordinate f i j).range = ⊥ ∨
        Function.Surjective (C.coordinate f i j) := by
    letI : IsSimpleGroup (C.factor j) := C.simple j
    rcases Subgroup.Normal.eq_bot_or_eq_top
      (H := (C.coordinate f i j).range) (hn i j) with h | h
    · exact Or.inl h
    · exact Or.inr (MonoidHom.range_eq_top.mp h)
  have hcoord_injective : Function.Injective (fun x p ↦ coord p x) := by
    intro x y hxy
    apply hi
    funext i
    apply C.equiv.injective
    funext j
    rcases hzero_or_full i j with hzero | hfull
    · have hx : C.coordinate f i j x = 1 := by
        rw [← Subgroup.mem_bot, ← hzero]
        exact ⟨x, rfl⟩
      have hy : C.coordinate f i j y = 1 := by
        rw [← Subgroup.mem_bot, ← hzero]
        exact ⟨y, rfl⟩
      exact hx.trans hy.symm
    · exact congrFun hxy ⟨(i, j), hfull⟩
  exact (semisimpleGroupChart_of_subdirect S
    (fun p ↦ C.centerless p.1.2) G coord (fun p ↦ p.2)
    hcoord_injective).some

end SemisimpleNormalChart

/-- A literal subgroup with full, jointly faithful simple coordinates gets
the chart required by the semisimple counting API. -/
def semisimpleNormalChart_of_subdirect_fin
    {U : Type} [Group U] (E : Subgroup U)
    (n : ℕ) (S : Fin n → Type)
    [∀ i, Group (S i)] [∀ i, Finite (S i)]
    [∀ i, IsSimpleGroup (S i)] (hcenterless : ∀ i, IsCenterless (S i))
    (f : ∀ i, E →* S i)
    (hs : ∀ i, Function.Surjective (f i))
    (hi : Function.Injective (fun x i ↦ f i x)) :
    SemisimpleNormalChart E :=
  (semisimpleGroupChart_of_subdirect_fin n S hcenterless E f hs hi).some.toNormalChart E

end SymmetricSubgroupAsymptotics

end
