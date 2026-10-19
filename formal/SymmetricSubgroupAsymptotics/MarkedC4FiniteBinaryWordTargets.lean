import SymmetricSubgroupAsymptotics.MarkedC4FiniteOrbitWordShapes

/-! One finite family of literal subdirect binary words, with a constructed
member for every original cutoff action. Both physical degree and the full
C4-character weight are preserved. Enumeration of this family is NOT an
input or a conclusion of this file. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.FiniteBinaryWordTargets
open FiniteOrbitWordShapes

abbrev LocalGroups {C b : ℕ} (S : Shape C b) :=
  ∀ i : Fin S.length.val,Subgroup (Equiv.Perm (Fin (S.degrees i).val))
abbrev Product {C b : ℕ} {S : Shape C b} (L : LocalGroups S) :=
  ∀ i : Fin S.length.val,L i

structure Target (C b : ℕ) where
  shape : Shape C b
  letters : LocalGroups shape
  binary : ∀ i,IsPGroup 2 (letters i)
  transitive : ∀ i (a d : Fin (shape.degrees i).val),∃ g : letters i,g.val a=d
  image : Subgroup (Product letters)
  subdirect : ∀ i,Function.Surjective (fun h : image => h.val i)

def Target.code {C b : ℕ} (T : Target C b) :
    Σ S : Shape C b,Σ L : LocalGroups S,Subgroup (Product L) :=
  ⟨T.shape,T.letters,T.image⟩

theorem Target.code_injective {C b : ℕ} : Function.Injective (@Target.code C b) := by
  intro S T h
  cases S
  cases T
  cases h
  rfl

instance {C b : ℕ} : Finite (Target C b) :=
  Finite.of_injective Target.code Target.code_injective
instance {C b : ℕ} : Fintype (Target C b) := Fintype.ofFinite _

variable {C b : ℕ} (G : Subgroup (PermutationGroup b))
  (hcut : OrbitCutoffFamilies.OrbitCutoff C G)

def actualLetters : LocalGroups (actualShape G hcut) := fun i =>
  ActualBinaryOrbitWord.Letter G ((number G).symm i)

def actualMap : G →* Product (actualLetters G hcut) where
  toFun g i := ActualBinaryOrbitWord.projection G ((number G).symm i) g
  map_one' := by funext i; exact (ActualBinaryOrbitWord.projection G _).map_one
  map_mul' g h := by funext i; exact (ActualBinaryOrbitWord.projection G _).map_mul g h

theorem actualMap_injective : Function.Injective (actualMap G hcut) := by
  intro g h he
  apply ActualBinaryOrbitWord.map_injective G
  funext i
  have hh := congrFun he (number G i)
  change ActualBinaryOrbitWord.projection G ((number G).symm (number G i)) g=
    ActualBinaryOrbitWord.projection G ((number G).symm (number G i)) h at hh
  rw [Equiv.symm_apply_apply] at hh
  exact hh

/-- Every field, including actual subdirectness, is constructed from G. -/
def actualTarget (hbin : IsPGroup 2 G) : Target C b where
  shape := actualShape G hcut
  letters := actualLetters G hcut
  binary i := ActualBinaryOrbitWord.letter_isPGroup G hbin ((number G).symm i)
  transitive i := ActualBinaryOrbitWord.letter_transitive G ((number G).symm i)
  image := (actualMap G hcut).range
  subdirect i := by
    intro l
    obtain ⟨g,hg⟩ := ActualBinaryOrbitWord.projection_surjective G ((number G).symm i) l
    exact ⟨(actualMap G hcut).rangeRestrict g,hg⟩

def originalEquiv (hbin : IsPGroup 2 G) : G ≃* (actualTarget G hcut hbin).image :=
  MonoidHom.ofInjective (actualMap_injective G hcut)

def homEquiv (hbin : IsPGroup 2 G) : (G →* Multiplicative (ZMod 4)) ≃
    ((actualTarget G hcut hbin).image →* Multiplicative (ZMod 4)) where
  toFun f := f.comp (originalEquiv G hcut hbin).symm.toMonoidHom
  invFun f := f.comp (originalEquiv G hcut hbin).toMonoidHom
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

theorem hom_card_eq (hbin : IsPGroup 2 G) : Nat.card (G →* Multiplicative (ZMod 4)) =
    Nat.card ((actualTarget G hcut hbin).image →* Multiplicative (ZMod 4)) :=
  Nat.card_congr (homEquiv G hcut hbin)

end SymmetricSubgroupAsymptotics.MarkedC4.FiniteBinaryWordTargets
