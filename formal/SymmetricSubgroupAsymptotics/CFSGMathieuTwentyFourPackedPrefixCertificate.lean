import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourRawNecessaryRelations
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
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPackedPrefixCertificate
open CFSGMathieuTwentyTwoFiveTransversalCover CFSGMathieuTwentyFourSharedSwapChart
open CFSGMathieuTwentyFourRawNecessaryRelations CFSGMathieuTwentyFourFixedProductRelations
open CFSGMathieuTwentyFourPackedFrameRows SignedPermutationWordPointEvaluation
open FiniteListBooleanReflection

abbrev First := Fin 22

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
  have hn0 : k.val.val ≠ 0 := fun he => k.property.1 (Fin.ext he)
  have hn1 : k.val.val ≠ 1 := fun he => k.property.2 (Fin.ext he)
  apply List.mem_map.mpr
  exact ⟨k.val.val-2,List.mem_range.mpr (by omega),by omega⟩

theorem mem_rawFourthDomain (l : Fourth) : l.val.val ∈ rawFourthDomain := by
  have hlt := l.val.isLt
  have hn := Finset.mem_compl.mp l.property
  simp only [CFSG.Certificates.Mathieu22.M22Certificates.SteinerSystem.blockB0,
    Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff] at hn
  apply List.mem_map.mpr
  exact ⟨l.val.val-5,List.mem_range.mpr (by omega),by omega⟩

theorem mem_rawFifthDomain (m : Fifth) : m.val.val ∈ rawFifthDomain := by
  rcases m.property with h | h | h <;> simp [rawFifthDomain,h]

/-- Raw selector interpreter, with no proof-bearing chart code in the loop. -/
def rawRelator (r i j k l m p : ℕ) : ℕ :=
  applyWord (packedGet productRow) (packedGet productInverseRow)
    (rawCandidateForward i j k l m) (rawCandidateInverse i j k l m)
    (relationWord ⟨r%7,Nat.mod_lt _ (by decide)⟩) p

theorem rawRelator_eq (r : Fin 7) (c : Code) (p : ℕ) :
    rawRelator r.val c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p=rawScalarRelation r c p := by
  unfold rawRelator
  simp only [Nat.mod_eq_of_lt r.isLt]
  rfl

theorem accepts_pointwise (c : Code) (h : Accepts c) (r : Fin 7) (p : Fin 24) :
    rawRelator r.val c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val=p.val := by
  rw [rawRelator_eq]
  exact accepts_rawScalarRelation c h r p

def codeCheck (i j : ℕ) (failure : Selector) (whitelist : List RawTail)
    (k l m : ℕ) : Bool :=
  whitelist.contains (k,(l,m)) ||
    (let n := failure k l m
     let r := (n / 24) % 7
     let p := n % 24
     !(rawRelator r i j k l m p == p))

def batchCheck (i j : ℕ) (failure : Selector) (whitelist : List RawTail) : Bool :=
  rawThirdDomain.all (fun k => rawFourthDomain.all (fun l =>
    rawFifthDomain.all (codeCheck i j failure whitelist k l)))

def failureRelator (failure : Selector) (t : Tail) : Fin 7 :=
  ⟨(failure t.1.val.val t.2.1.val.val t.2.2.val.val / 24) % 7,Nat.mod_lt _ (by decide)⟩

def failurePoint (failure : Selector) (t : Tail) : Fin 24 :=
  ⟨failure t.1.val.val t.2.1.val.val t.2.2.val.val % 24,Nat.mod_lt _ (by decide)⟩

theorem accepts_coordinates_mem (i : First) (j : Second)
    (failure : Selector) (whitelist : List RawTail)
    (hbatch : batchCheck i.val j.val.val failure whitelist = true)
    (t : Tail)
    (h : CFSGMathieuTwentyFourFixedProductRelations.Accepts (code i j t)) :
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
    Finset (Equiv.Perm (Fin 24)) := by
  classical
  exact (whitelist.map (fun q => sharedSwapDecode (code i j (realize q)))).toFinset

theorem accepts_mem_acceptedElements (i : First) (j : Second)
    (failure : Selector) (whitelist : List RawTail)
    (hbatch : batchCheck i.val j.val.val failure whitelist = true)
    (c : Code) (hfirst : c.1.1 = i) (hsecond : c.1.2 = j)
    (h : CFSGMathieuTwentyFourFixedProductRelations.Accepts c) :
    sharedSwapDecode c ∈ acceptedElements i j whitelist := by
  classical
  rcases c with ⟨⟨a,b⟩,⟨k,⟨l,m⟩⟩⟩
  change a = i at hfirst
  change b = j at hsecond
  subst a
  subst b
  let t : Tail := (k,(l,m))
  have hw : coordinates t ∈ whitelist := accepts_coordinates_mem i j failure whitelist hbatch t h
  change sharedSwapDecode (code i j t) ∈
    (whitelist.map (fun q => sharedSwapDecode (code i j (realize q)))).toFinset
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨coordinates t,hw,?_⟩
  rw [realize_coordinates]

theorem acceptedElements_card_le_length (i : First) (j : Second) (whitelist : List RawTail) :
    (acceptedElements i j whitelist).card ≤ whitelist.length := by
  classical
  change (whitelist.map (fun q => sharedSwapDecode (code i j (realize q)))).toFinset.card ≤ whitelist.length
  simpa only [List.length_map] using
    (List.toFinset_card_le (whitelist.map (fun q => sharedSwapDecode (code i j (realize q)))))

/-- The actual set of accepted original permutation images in this prefix. -/
def acceptingImages (i : First) (j : Second) : Type :=
  {u : Equiv.Perm (Fin 24) // ∃ t : Tail,
    CFSGMathieuTwentyFourFixedProductRelations.Accepts (code i j t) ∧
      u = sharedSwapDecode (code i j t)}

theorem acceptingImages_card_le_length (i : First) (j : Second)
    (failure : Selector) (whitelist : List RawTail)
    (hbatch : batchCheck i.val j.val.val failure whitelist = true) :
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

theorem swapFibre_image_mem_acceptedElements [IsSimpleGroup CFSG.Models.Presentations.M24.Model] (i : First) (j : Second)
    (failure : Selector) (whitelist : List RawTail)
    (hbatch : batchCheck i.val j.val.val failure whitelist = true)
    (f : CFSGMathieuTwentyFourSwapFibreOuterReduction.SwapFibre)
    (c : Code)
    (hc : sharedSwapDecode c =
      CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
        (f.val.val CFSGMathieuTwentyFourGoodSylowTwentyThree.pinnedX))
    (hfirst : c.1.1 = i) (hsecond : c.1.2 = j) :
    CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
      (f.val.val CFSGMathieuTwentyFourGoodSylowTwentyThree.pinnedX) ∈
        acceptedElements i j whitelist := by
  rw [←hc]
  apply accepts_mem_acceptedElements i j failure whitelist hbatch c hfirst hsecond
  intro r
  change relationValue r
    (CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
      CFSGMathieuTwentyFourSwapFibreOuterReduction.product) (sharedSwapDecode c)=1
  exact (congrArg (fun u => relationValue r
    (CFSGMathieuTwentyFourActualRepresentation.permutationRepresentation
      CFSGMathieuTwentyFourSwapFibreOuterReduction.product) u) hc).trans
    (CFSGMathieuTwentyFourFixedProductRelations.fixed_image_relations f.val r)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyFourPackedPrefixCertificate
