import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedPointEncoding
import SymmetricSubgroupAsymptotics.FiniteListBooleanReflection
import Mathlib.Data.Finset.Card

/-! Generic semantic consumer for ONE fixed first/second chart prefix.
A proved960 Bool equality gives a literal finite cover of the SAME actual
accepted permutation images. Whitelist length is arbitrary; no capacity
or automorphism/presentation converse is assumed. Invalid whitelist
entries add at most one image each. Raw checking contains no Fin/proofs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedPrefixCertificate
open CFSGMathieuTwentyThreeStabilizerTransversalCover CFSGMathieuTwentyThreeNormalizedFibreChart
open CFSGMathieuTwentyThreePackedPointEncoding FiniteListBooleanReflection

abbrev Tail : Type := Third × (Fourth × Fifth)
abbrev RawTail : Type := ℕ × (ℕ × ℕ)
abbrev Selector : Type := ℕ → ℕ → ℕ → ℕ

def coordinates (t : Tail) : RawTail := (t.1.val.val,(t.2.1.val.val,t.2.2.val.val))

def code (i : First) (j : Second) (t : Tail) : Code := ((i,j),(t.1,(t.2.1,t.2.2)))

theorem coordinates_injective : Function.Injective coordinates := by
  rintro ⟨k,⟨l,m⟩⟩ ⟨k',⟨l',m'⟩⟩ h
  have hk : k = k' := Subtype.ext (Fin.ext (congrArg (fun q : RawTail => q.1) h))
  have hl : l = l' := Subtype.ext (Fin.ext (congrArg (fun q : RawTail => q.2.1) h))
  have hm : m = m' := Subtype.ext (Fin.ext (congrArg (fun q : RawTail => q.2.2) h))
  subst k'
  subst l'
  subst m'
  rfl

private def defaultTail : Tail := (⟨2,by decide⟩,(⟨5,by decide⟩,⟨3,by decide⟩))

def realize (q : RawTail) : Tail := by
  classical
  exact if h : ∃ t : Tail, coordinates t = q then Classical.choose h else defaultTail

theorem realize_coordinates (t : Tail) : realize (coordinates t) = t := by
  classical
  have h : ∃ u : Tail, coordinates u = coordinates t := ⟨t,rfl⟩
  simp only [realize,dif_pos h]
  exact coordinates_injective (Classical.choose_spec h)

def rawThirdDomain : List ℕ := (List.range 20).map (fun n => n+2)
def rawFourthDomain : List ℕ := (List.range 16).map (fun n => n+5)
def rawFifthDomain : List ℕ := [3,4,21]

theorem mem_rawThirdDomain (k : Third) : k.val.val ∈ rawThirdDomain := by
  have hlt := k.val.isLt
  have hn22 : k.val.val ≠ 22 := fun he => k.property.1 (Fin.ext he)
  have hn0 : k.val.val ≠ 0 := fun he => k.property.2.1 (Fin.ext he)
  have hn1 : k.val.val ≠ 1 := fun he => k.property.2.2 (Fin.ext he)
  apply List.mem_map.mpr
  refine ⟨k.val.val-2,List.mem_range.mpr (by omega),by omega⟩

theorem mem_rawFourthDomain (l : Fourth) : l.val.val ∈ rawFourthDomain := by
  have hlt := l.val.isLt
  have hn := Finset.mem_compl.mp l.property
  simp only [CFSG.Certificates.Mathieu23.M23Certificates.SteinerSystem.blockB0,
    Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff] at hn
  apply List.mem_map.mpr
  refine ⟨l.val.val-5,List.mem_range.mpr (by omega),by omega⟩

theorem mem_rawFifthDomain (m : Fifth) : m.val.val ∈ rawFifthDomain := by
  rcases m.property with h | h | h <;> simp [rawFifthDomain,h]

def codeCheck (i j : ℕ) (failure : Selector) (whitelist : List RawTail)
    (k l m : ℕ) : Bool :=
  whitelist.contains (k,(l,m)) ||
    (let n := failure k l m
     let r := (n / 23) % 9
     let p := n % 23
     !(rawRelator r i j k l m p == p))

def batchCheck (i j : ℕ) (failure : Selector) (whitelist : List RawTail) : Bool :=
  rawThirdDomain.all (fun k => rawFourthDomain.all (fun l =>
    rawFifthDomain.all (codeCheck i j failure whitelist k l)))

def failureRelator (failure : Selector) (t : Tail) : Fin 9 :=
  ⟨(failure t.1.val.val t.2.1.val.val t.2.2.val.val / 23) % 9,Nat.mod_lt _ (by decide)⟩

def failurePoint (failure : Selector) (t : Tail) : Fin 23 :=
  ⟨failure t.1.val.val t.2.1.val.val t.2.2.val.val % 23,Nat.mod_lt _ (by decide)⟩

theorem accepts_coordinates_mem (i : First) (j : Second)
    (failure : Selector) (whitelist : List RawTail)
    (hbatch : batchCheck i.val.val j.val.val failure whitelist = true)
    (t : Tail)
    (h : CFSGMathieuTwentyThreeProductNecessaryRelations.Accepts (decodeAtZero (code i j t)).val) :
    coordinates t ∈ whitelist := by
  have hk := all_true_at rawThirdDomain _ hbatch t.1.val.val (mem_rawThirdDomain t.1)
  have hl := all_true_at rawFourthDomain _ hk t.2.1.val.val (mem_rawFourthDomain t.2.1)
  have hm := all_true_at rawFifthDomain _ hl t.2.2.val.val (mem_rawFifthDomain t.2.2)
  change (whitelist.contains (coordinates t) || _) = true at hm
  rw [Bool.or_eq_true_eq_eq_true_or_eq_true] at hm
  rcases hm with hw | hn
  · exact List.contains_iff_mem.mp hw
  · exfalso
    apply not_beq_sound _ _ hn
    exact accepts_pointwise (code i j t) h (failureRelator failure t) (failurePoint failure t)

def acceptedElements (i : First) (j : Second) (whitelist : List RawTail) :
    Finset (Equiv.Perm (Fin 23)) := by
  classical
  exact (whitelist.map (fun q => (decodeAtZero (code i j (realize q))).val)).toFinset

theorem accepts_mem_acceptedElements (i : First) (j : Second)
    (failure : Selector) (whitelist : List RawTail)
    (hbatch : batchCheck i.val.val j.val.val failure whitelist = true)
    (c : Code) (hfirst : c.1.1 = i) (hsecond : c.1.2 = j)
    (h : CFSGMathieuTwentyThreeProductNecessaryRelations.Accepts (decodeAtZero c).val) :
    (decodeAtZero c).val ∈ acceptedElements i j whitelist := by
  classical
  rcases c with ⟨⟨a,b⟩,⟨k,⟨l,m⟩⟩⟩
  change a = i at hfirst
  change b = j at hsecond
  subst a
  subst b
  let t : Tail := (k,(l,m))
  have hw : coordinates t ∈ whitelist := accepts_coordinates_mem i j failure whitelist hbatch t h
  change (decodeAtZero (code i j t)).val ∈
    (whitelist.map (fun q => (decodeAtZero (code i j (realize q))).val)).toFinset
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨coordinates t,hw,?_⟩
  rw [realize_coordinates]

theorem acceptedElements_card_le_length (i : First) (j : Second) (whitelist : List RawTail) :
    (acceptedElements i j whitelist).card ≤ whitelist.length := by
  classical
  change (whitelist.map (fun q => (decodeAtZero (code i j (realize q))).val)).toFinset.card ≤ whitelist.length
  simpa only [List.length_map] using
    (List.toFinset_card_le (whitelist.map (fun q => (decodeAtZero (code i j (realize q))).val)))

/-- The actual set of accepted original permutation images in this prefix. -/
def acceptingImages (i : First) (j : Second) : Type :=
  {u : Equiv.Perm (Fin 23) // ∃ t : Tail,
    CFSGMathieuTwentyThreeProductNecessaryRelations.Accepts (decodeAtZero (code i j t)).val ∧
      u = (decodeAtZero (code i j t)).val}

theorem acceptingImages_card_le_length (i : First) (j : Second)
    (failure : Selector) (whitelist : List RawTail)
    (hbatch : batchCheck i.val.val j.val.val failure whitelist = true) :
    Nat.card (acceptingImages i j) ≤ whitelist.length := by
  classical
  let embed : acceptingImages i j → acceptedElements i j whitelist := fun u =>
    ⟨u.val,by
      obtain ⟨t,ht,he⟩ := u.property
      rw [he]
      exact accepts_mem_acceptedElements i j failure whitelist hbatch (code i j t) rfl rfl ht⟩
  have hinj : Function.Injective embed := by
    intro u v he
    exact Subtype.ext (congrArg
      (fun q : acceptedElements i j whitelist => q.val) he)
  have hcard := Nat.card_le_card_of_injective embed hinj
  have hsmall : Nat.card (acceptingImages i j) ≤ (acceptedElements i j whitelist).card := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hcard
  exact hsmall.trans (acceptedElements_card_le_length i j whitelist)

theorem pointFibre_image_mem_acceptedElements (i : First) (j : Second)
    (failure : Selector) (whitelist : List RawTail)
    (hbatch : batchCheck i.val.val j.val.val failure whitelist = true)
    (f : CFSGMathieuTwentyThreeNormalizedFixedPointFibre.pointFibre 0)
    (c : Code)
    (hc : (decodeAtZero c).val =
      CFSGMathieuTwentyThreeActualRepresentation.permutationRepresentation
        (f.val.val CFSGMathieuTwentyThreeGoodSylowTwentyThree.pinnedX))
    (hfirst : c.1.1 = i) (hsecond : c.1.2 = j) :
    CFSGMathieuTwentyThreeActualRepresentation.permutationRepresentation
      (f.val.val CFSGMathieuTwentyThreeGoodSylowTwentyThree.pinnedX) ∈
        acceptedElements i j whitelist := by
  rw [←hc]
  apply accepts_mem_acceptedElements i j failure whitelist hbatch c hfirst hsecond
  rw [hc]
  exact CFSGMathieuTwentyThreeProductNecessaryRelations.accepts_of_fixed_product f.val

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyThreePackedPrefixCertificate
