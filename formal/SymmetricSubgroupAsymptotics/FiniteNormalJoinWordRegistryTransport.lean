import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry

/-!
# Transport selected normal-join word registries

Compact normality and join words commute with a checked group equivalence.
This transports the row-index registry to the literal permutation subgroup
without adding a normal-list or completeness assumption.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G H ι κ τ : Type*} [Group G] [Group H]

namespace FiniteGeneratorWordCertificate

variable {source : ι → G} {target : κ → G}
    (C : FiniteGeneratorWordCertificate source target)

/-- Apply a group equivalence to every literal generator and equation. -/
def mapEquiv (e : G ≃* H) :
    FiniteGeneratorWordCertificate
      (fun i => e (source i)) (fun j => e (target j)) where
  words := C.words
  equations i :=
    calc
      (C.words i).eval (fun j => e (target j)) =
          e ((C.words i).eval target) := by
        simpa only [MulEquiv.coe_toMonoidHom] using
          (FiniteGeneratorWord.map_eval e.toMonoidHom target
            (C.words i)).symm
      _ = e (source i) := congrArg e (C.equations i)

end FiniteGeneratorWordCertificate

namespace FiniteNormalityWordCertificate

variable {ambient : ι → G} {state : κ → G}
    (C : FiniteNormalityWordCertificate ambient state)

/-- Transport all checked normality words across the equivalence. -/
def mapEquiv (e : G ≃* H) :
    FiniteNormalityWordCertificate
      (fun i => e (ambient i)) (fun j => e (state j)) where
  positiveWords := C.positiveWords
  positiveEquations i j :=
    calc
      (C.positiveWords i j).eval (fun j => e (state j)) =
          e ((C.positiveWords i j).eval state) := by
        simpa only [MulEquiv.coe_toMonoidHom] using
          (FiniteGeneratorWord.map_eval e.toMonoidHom state
            (C.positiveWords i j)).symm
      _ = e (ambient i * state j * (ambient i)⁻¹) :=
        congrArg e (C.positiveEquations i j)
      _ = e (ambient i) * e (state j) * (e (ambient i))⁻¹ := by
        simp only [map_mul, map_inv]
  negativeWords := C.negativeWords
  negativeEquations i j :=
    calc
      (C.negativeWords i j).eval (fun j => e (state j)) =
          e ((C.negativeWords i j).eval state) := by
        simpa only [MulEquiv.coe_toMonoidHom] using
          (FiniteGeneratorWord.map_eval e.toMonoidHom state
            (C.negativeWords i j)).symm
      _ = e ((ambient i)⁻¹ * state j * ambient i) :=
        congrArg e (C.negativeEquations i j)
      _ = (e (ambient i))⁻¹ * e (state j) * e (ambient i) := by
        simp only [map_mul, map_inv]

end FiniteNormalityWordCertificate

namespace FiniteNormalJoinWord

/-- Map every literal group element in a normal-join word. -/
def map (e : G →* H) : FiniteNormalJoinWord κ G → FiniteNormalJoinWord κ H
  | .one => .one
  | .parent i => .parent i
  | .conjugate g => .conjugate (e g)
  | .mul u v => .mul (u.map e) (v.map e)
  | .inv u => .inv (u.map e)

theorem eval_map (e : G →* H) (parent : κ → G) (representative : G)
    (word : FiniteNormalJoinWord κ G) :
    (word.map e).eval (parent := fun i => e (parent i)) (e representative) =
      e (word.eval (parent := parent) representative) := by
  induction word <;> simp_all only [map, eval, map_one, map_mul, map_inv]

end FiniteNormalJoinWord

namespace FiniteNormalJoinTransitionCertificate

variable {parent : κ → G} {representative : G} {child : τ → G}
    (C : FiniteNormalJoinTransitionCertificate parent representative child)

/-- Transport one exact parent/normal-closure/child transition. -/
def mapEquiv (e : G ≃* H) :
    FiniteNormalJoinTransitionCertificate
      (fun i => e (parent i)) (e representative) (fun j => e (child j)) where
  parentToChild := C.parentToChild.mapEquiv e
  representativeWord := C.representativeWord
  representativeEquation :=
    calc
      C.representativeWord.eval (fun j => e (child j)) =
          e (C.representativeWord.eval child) := by
        simpa only [MulEquiv.coe_toMonoidHom] using
          (FiniteGeneratorWord.map_eval e.toMonoidHom child
            C.representativeWord).symm
      _ = e representative := congrArg e C.representativeEquation
  childWords j := (C.childWords j).map e.toMonoidHom
  childEquations j :=
    calc
      ((C.childWords j).map e.toMonoidHom).eval
          (parent := fun i => e (parent i)) (e representative) =
          e ((C.childWords j).eval (parent := parent) representative) := by
        simpa only [MulEquiv.coe_toMonoidHom] using
          FiniteNormalJoinWord.eval_map e.toMonoidHom parent representative
            (C.childWords j)
      _ = e (child j) := congrArg e (C.childEquations j)

end FiniteNormalJoinTransitionCertificate

theorem range_equiv_image {I : Type*} (e : G ≃* H) (f : I → G) :
    e.toMonoidHom '' Set.range f = Set.range (fun i => e (f i)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨f i, ⟨i, rfl⟩, rfl⟩

theorem map_bot_equiv (e : G ≃* H) :
    (⊥ : Subgroup G).map e.toMonoidHom = ⊥ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy_one : y = 1 := hy
    subst y
    simp
  · intro hx
    have hx_one : x = 1 := hx
    subst x
    exact ⟨1, by simp, by simp⟩

theorem closure_range_map_equiv {I : Type*} (e : G ≃* H) (f : I → G) :
    Subgroup.closure (Set.range (fun i => e (f i))) =
      (Subgroup.closure (Set.range f)).map e.toMonoidHom := by
  rw [MonoidHom.map_closure, range_equiv_image]

namespace FiniteNormalJoinWordRegistryData

variable {I : Type*} [Finite G] [Finite H] {c : ℕ}
    {representative : Fin c → G}
    {C : FiniteConjugacyCardinalCover representative}
    {ambient : ι → G} {stateGenerators : I → κ → G}
    (D : FiniteNormalJoinWordRegistryData C ambient stateGenerators)

/-- Transport the complete checked registry to a corresponding conjugacy
cover in the literal target group. -/
noncomputable def mapEquiv (e : G ≃* H)
    (C' : FiniteConjugacyCardinalCover (fun i => e (representative i))) :
    FiniteNormalJoinWordRegistryData C'
      (fun i => e (ambient i)) (fun s j => e (stateGenerators s j)) where
  ambient_full := by
    rw [closure_range_map_equiv, D.ambient_full]
    exact Subgroup.map_top_of_surjective e.toMonoidHom e.surjective
  normality i := (D.normality i).mapEquiv e
  bottom := D.bottom
  bottom_eq := by
    rw [closure_range_map_equiv, D.bottom_eq, map_bot_equiv]
  child := D.child
  transition i j := (D.transition i j).mapEquiv e

end FiniteNormalJoinWordRegistryData

end SymmetricSubgroupAsymptotics

end
