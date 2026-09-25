import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-!
# Reflected Cayley certificates with parent witnesses

A faithful encoding and an executable right-generator action allow all
finite checks to concern compact codes. Parent transitions construct the
actual group elements and their words; no word product is recomputed by a
finite decision procedure. The soundness theorem produces the same literal
Cayley certificate used by the original kernel/image checks.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G ι Code : Type*} [Group G]

/-- A faithful code for the original group, with a specified executable
right action of its original generators. -/
structure GeneratorEncoding (generators : ι → G) (Code : Type*) where
  encode : G → Code
  injective : Function.Injective encode
  one : Code
  encode_one : encode 1 = one
  step : Code → ι → Code
  encode_step : ∀ g j, encode (g * generators j) = step (encode g) j

/-- Untrusted finite code rows. Local predecessor edges certify reachability
without evaluating a whole group word for every row. -/
structure EncodedCayleyCertificate {generators : ι → G}
    (E : GeneratorEncoding generators Code) (n : ℕ) where
  rows : Fin n → Code
  identity : Fin n
  identity_eq : rows identity = E.one
  next : Fin n → ι → Fin n
  next_eq : ∀ i j, rows (next i j) = E.step (rows i) j
  rank : Fin n → ℕ
  parent : ∀ i, i ≠ identity → Fin n
  letter : ∀ i, i ≠ identity → ι
  parent_lt : ∀ i h, rank (parent i h) < rank i
  parent_next : ∀ i h, next (parent i h) (letter i h) = i

namespace EncodedCayleyCertificate

variable {generators : ι → G} {E : GeneratorEncoding generators Code} {n : ℕ}
    (C : EncodedCayleyCertificate E n)

/-- A certified word is constructed by following strictly smaller parents. -/
def words (i : Fin n) : List ι :=
  if hi : i = C.identity then []
  else words (C.parent i hi) ++ [C.letter i hi]
termination_by C.rank i
decreasing_by exact C.parent_lt i hi

@[simp] theorem words_identity : C.words C.identity = [] := by
  rw [words]
  simp

theorem words_parent (i : Fin n) (hi : i ≠ C.identity) :
    C.words i = C.words (C.parent i hi) ++ [C.letter i hi] := by
  rw [words]
  simp only [dif_neg hi]

/-- Every code row encodes an actual original group word. -/
theorem encode_word (i : Fin n) :
    E.encode (((C.words i).map generators).prod) = C.rows i := by
  by_cases hi : i = C.identity
  · subst i
    simp only [C.words_identity, List.map_nil, List.prod_nil,
      E.encode_one, C.identity_eq]
  · rw [C.words_parent i hi, List.map_append, List.prod_append,
      List.map_singleton, List.prod_singleton, E.encode_step,
      encode_word (C.parent i hi), ← C.next_eq, C.parent_next]
termination_by C.rank i
decreasing_by exact C.parent_lt i hi

/-- Soundness: compact numeric checks produce an actual Cayley certificate
in the original group, with its original generator order. -/
def toCayley : FiniteCayleyCertificate generators n where
  elements i := ((C.words i).map generators).prod
  identity := C.identity
  identity_eq := by simp only [C.words_identity, List.map_nil, List.prod_nil]
  next := C.next
  next_eq := by
    intro i j
    apply E.injective
    rw [C.encode_word, E.encode_step, C.encode_word, C.next_eq]
  words := C.words
  words_eq := fun _ => rfl

@[simp] theorem encode_elements (i : Fin n) :
    E.encode (C.toCayley.elements i) = C.rows i := C.encode_word i

/-- Code injectivity certifies the actual group cardinality, rather than
accepting a cardinality declared by a data producer. -/
theorem card_closure [Finite G] (hinj : Function.Injective C.rows) :
    Nat.card (Subgroup.closure (Set.range generators)) = n := by
  apply C.toCayley.card_closure
  intro i j he
  apply hinj
  simpa only [C.encode_elements] using congrArg E.encode he

/-- Literal generated-subgroup membership is exactly code-row membership. -/
theorem mem_closure_iff [Finite G] (g : G) :
    g ∈ Subgroup.closure (Set.range generators) ↔ ∃ i, C.rows i = E.encode g := by
  rw [C.toCayley.mem_closure_iff]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i,(C.encode_elements i).symm⟩
  · rintro ⟨i,hi⟩
    exact ⟨i,E.injective ((C.encode_elements i).trans hi)⟩

/-- Tests of an arbitrary predicate can be checked on compact code rows
and then transported to all members of the literal generated subgroup. -/
theorem forall_mem_closure [Finite G] (P : G → Prop) (test : Code → Prop)
    (sound : ∀ g, test (E.encode g) → P g)
    (checked : ∀ i, test (C.rows i)) :
    ∀ g ∈ Subgroup.closure (Set.range generators), P g := by
  intro g hg
  obtain ⟨i,hi⟩ := (C.mem_closure_iff g).mp hg
  exact sound g (hi ▸ checked i)

end EncodedCayleyCertificate

/-- Faithful encodings compose without losing the original generator maps. -/
def GeneratorEncoding.prod {H D : Type*} [Group H]
    {s : ι → G} {t : ι → H} (E : GeneratorEncoding s Code)
    (F : GeneratorEncoding t D) :
    GeneratorEncoding (fun i => (s i,t i)) (Code × D) where
  encode g := (E.encode g.1,F.encode g.2)
  injective := by
    intro x y h
    exact Prod.ext (E.injective (congrArg Prod.fst h))
      (F.injective (congrArg Prod.snd h))
  one := (E.one,F.one)
  encode_one := Prod.ext E.encode_one F.encode_one
  step c i := (E.step c.1 i,F.step c.2 i)
  encode_step g i := Prod.ext (E.encode_step g.1 i) (F.encode_step g.2 i)

end SymmetricSubgroupAsymptotics
