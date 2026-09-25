import SymmetricSubgroupAsymptotics.OddMarker
import Mathlib.GroupTheory.Goursat
import Mathlib.GroupTheory.PGroup

/-!
# Contraction of the complete exterior through its maximal binary quotient

The residual is the actual intersection of normal subgroups with 2-group
quotient. Full exterior projection forces its entire copy into every subgroup
of a binary product with that exterior. The correspondence retains the whole
projection inside the binary product and therefore every original factor test.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable (T : Type*) [Group T]

/-- Literal normal kernels whose quotient is a 2-group. -/
def TerminalBinaryKernel :=
  {N : Subgroup T // ∃ hN : N.Normal, letI := hN; IsPGroup 2 (T ⧸ N)}

instance (N : TerminalBinaryKernel T) : N.1.Normal := N.2.choose

theorem terminalBinaryKernel_quotient (N : TerminalBinaryKernel T) :
    IsPGroup 2 (T ⧸ N.1) := N.2.choose_spec

/-- The binary residual O²(T), retaining every actual normal kernel. -/
def terminalTwoResidual : Subgroup T := ⨅ N : TerminalBinaryKernel T, N.1

instance : (terminalTwoResidual T).Normal :=
  Subgroup.normal_iInf_normal (fun _ => inferInstance)

theorem terminalTwoResidual_le (N : Subgroup T) [N.Normal]
    (hN : IsPGroup 2 (T ⧸ N)) : terminalTwoResidual T ≤ N :=
  iInf_le _ (⟨N,inferInstance,hN⟩ : TerminalBinaryKernel T)

/-- Every map to a binary group kills the residual. -/
theorem terminalTwoResidual_le_ker {Q : Type*} [Group Q]
    (f : T →* Q) (hQ : IsPGroup 2 Q) : terminalTwoResidual T ≤ f.ker := by
  apply terminalTwoResidual_le
  exact (hQ.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm

instance [Finite T] : Finite (TerminalBinaryKernel T) :=
  inferInstanceAs (Finite {N : Subgroup T // ∃ hN : N.Normal, letI := hN; IsPGroup 2 (T ⧸ N)})

/-- For a finite exterior this is itself a binary quotient, so the literal
intersection has the promised maximal-quotient meaning. -/
theorem terminalTwoResidual_quotient_binary [Finite T] :
    IsPGroup 2 (T ⧸ terminalTwoResidual T) := by
  classical
  letI := Fintype.ofFinite (TerminalBinaryKernel T)
  intro x
  obtain ⟨t,rfl⟩ := QuotientGroup.mk'_surjective (terminalTwoResidual T) x
  choose k hk using fun N : TerminalBinaryKernel T => terminalBinaryKernel_quotient T N
    ((QuotientGroup.mk' N.1) t)
  let m : ℕ := ∑ N, k N
  refine ⟨m,?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  rw [terminalTwoResidual, Subgroup.mem_iInf]
  intro N
  have hkm : k N ≤ m := Finset.single_le_sum (fun i _ => Nat.zero_le (k i)) (Finset.mem_univ N)
  have hexp : (2 : ℕ)^m = 2^(k N)*2^(m-k N) := by
    rw [← pow_add, Nat.add_sub_of_le hkm]
  have hpow : ((QuotientGroup.mk' N.1) t) ^ (2^m) = 1 := by
    rw [hexp,pow_mul,hk N,one_pow]
  rw [← map_pow] at hpow
  exact (QuotientGroup.eq_one_iff _).mp hpow

variable {T} {D : Type*} [Group D]

/-- The common exterior quotient is binary even when the projection inside
D is proper. This proves the needed Goursat consequence directly by powers. -/
theorem terminal_goursat_quotient_binary (hD : IsPGroup 2 D)
    (H : Subgroup (D × T)) [H.goursatSnd.Normal]
    (hfull : H.map (MonoidHom.snd D T) = ⊤) :
    IsPGroup 2 (T ⧸ H.goursatSnd) := by
  intro x
  obtain ⟨t,rfl⟩ := QuotientGroup.mk'_surjective H.goursatSnd x
  have ht : t ∈ H.map (MonoidHom.snd D T) := by rw [hfull]; trivial
  obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp ht
  obtain ⟨k,hk⟩ := hD a.1
  refine ⟨k,?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply Subgroup.mem_goursatSnd.mpr
  have hpow := H.pow_mem ha (2^k)
  have heq : a^(2^k) = (1,t^(2^k)) := by
    apply Prod.ext
    · exact hk
    · change a.2^(2^k) = t^(2^k)
      change a.2 = t at he
      rw [he]
  rwa [heq] at hpow

/-- Every exterior-full subgroup contains the entire residual on that
exterior alone. No independence of its internal coordinates is required. -/
theorem terminal_forced_residual (hD : IsPGroup 2 D)
    (H : Subgroup (D × T)) (hfull : H.map (MonoidHom.snd D T) = ⊤)
    (t : T) (ht : t ∈ terminalTwoResidual T) : (1,t) ∈ H := by
  have hsurj : Function.Surjective (Prod.snd ∘ H.subtype) := by
    intro s
    have hs : s ∈ H.map (MonoidHom.snd D T) := by rw [hfull]; trivial
    obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨x,hx⟩,he⟩
  letI := H.normal_goursatSnd hsurj
  have hq : IsPGroup 2 (T ⧸ H.goursatSnd) := terminal_goursat_quotient_binary hD H hfull
  exact Subgroup.mem_goursatSnd.mp (terminalTwoResidual_le T H.goursatSnd hq ht)

/-- Quotient only the complete exterior; keep the binary product literally. -/
def terminalContraction : D × T →* D × (T ⧸ terminalTwoResidual T) :=
  (MonoidHom.id D).prodMap (QuotientGroup.mk' (terminalTwoResidual T))

theorem terminalContraction_surjective :
    Function.Surjective (terminalContraction (D := D) (T := T)) := by
  rintro ⟨d,t⟩
  obtain ⟨s,hs⟩ := QuotientGroup.mk'_surjective (terminalTwoResidual T) t
  exact ⟨(d,s),Prod.ext rfl hs⟩

theorem terminalContraction_ker_le (hD : IsPGroup 2 D)
    (H : Subgroup (D × T)) (hfull : H.map (MonoidHom.snd D T) = ⊤) :
    (terminalContraction (D := D) (T := T)).ker ≤ H := by
  rintro ⟨d,t⟩ h
  change (d,(QuotientGroup.mk' (terminalTwoResidual T)) t) = (1,1) at h
  rcases Prod.mk.inj h with ⟨rfl,ht⟩
  exact terminal_forced_residual hD H hfull t ((QuotientGroup.eq_one_iff _).mp ht)

/-- Contraction preserves the entire subgroup projected inside D. -/
theorem terminalContraction_product_image (H : Subgroup (D × T)) :
    (H.map terminalContraction).map (MonoidHom.fst D (T ⧸ terminalTwoResidual T)) =
      H.map (MonoidHom.fst D T) := by
  rw [Subgroup.map_map]
  rfl

/-- The quotient image remains full on the whole contracted exterior. -/
theorem terminalContraction_full (H : Subgroup (D × T))
    (hfull : H.map (MonoidHom.snd D T) = ⊤) :
    (H.map terminalContraction).map (MonoidHom.snd D (T ⧸ terminalTwoResidual T)) = ⊤ := by
  have hcomp : (MonoidHom.snd D (T ⧸ terminalTwoResidual T)).comp terminalContraction =
      (QuotientGroup.mk' (terminalTwoResidual T)).comp (MonoidHom.snd D T) := rfl
  rw [Subgroup.map_map,hcomp,← Subgroup.map_map,hfull]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

/-- Full preimage restores the entire original exterior. -/
theorem terminalContraction_comap_full
    (J : Subgroup (D × (T ⧸ terminalTwoResidual T)))
    (hfull : J.map (MonoidHom.snd D (T ⧸ terminalTwoResidual T)) = ⊤) :
    (J.comap terminalContraction).map (MonoidHom.snd D T) = ⊤ := by
  apply top_unique
  intro t _
  have ht : (QuotientGroup.mk' (terminalTwoResidual T)) t ∈
      J.map (MonoidHom.snd D (T ⧸ terminalTwoResidual T)) := by rw [hfull]; trivial
  obtain ⟨x,hx,he⟩ := Subgroup.mem_map.mp ht
  refine Subgroup.mem_map.mpr ⟨(x.1,t),?_,rfl⟩
  change (x.1,(QuotientGroup.mk' (terminalTwoResidual T)) t) ∈ J
  change x.2 = (QuotientGroup.mk' (terminalTwoResidual T)) t at he
  simpa only [← he] using hx

theorem terminalContraction_comap_product_image
    (J : Subgroup (D × (T ⧸ terminalTwoResidual T))) :
    (J.comap terminalContraction).map (MonoidHom.fst D T) =
      J.map (MonoidHom.fst D (T ⧸ terminalTwoResidual T)) := by
  have h := terminalContraction_product_image (J.comap terminalContraction)
  rw [Subgroup.map_comap_eq_self_of_surjective terminalContraction_surjective] at h
  exact h.symm

/-- The complete-exterior terminal correspondence with every condition on
its actual binary-product image retained. -/
def terminalContractionEquiv (hD : IsPGroup 2 D) (P : Subgroup D → Prop) :
    {H : Subgroup (D × T) // H.map (MonoidHom.snd D T) = ⊤ ∧
      P (H.map (MonoidHom.fst D T))} ≃
    {J : Subgroup (D × (T ⧸ terminalTwoResidual T)) //
      J.map (MonoidHom.snd D (T ⧸ terminalTwoResidual T)) = ⊤ ∧
      P (J.map (MonoidHom.fst D (T ⧸ terminalTwoResidual T)))} where
  toFun H := ⟨H.1.map terminalContraction,terminalContraction_full H.1 H.2.1,
    by simpa only [terminalContraction_product_image] using H.2.2⟩
  invFun J := ⟨J.1.comap terminalContraction,terminalContraction_comap_full J.1 J.2.1,
    by simpa only [terminalContraction_comap_product_image] using J.2.2⟩
  left_inv H := Subtype.ext (Subgroup.comap_map_eq_self (terminalContraction_ker_le hD H.1 H.2.1))
  right_inv J := Subtype.ext
    (Subgroup.map_comap_eq_self_of_surjective terminalContraction_surjective J.1)

/-- Exact terminal cardinality, with the original complete exterior and all
conditions on the whole binary-product image retained. -/
theorem terminalContraction_card (hD : IsPGroup 2 D) (P : Subgroup D → Prop) :
    Nat.card {H : Subgroup (D × T) // H.map (MonoidHom.snd D T) = ⊤ ∧
      P (H.map (MonoidHom.fst D T))} =
    Nat.card {J : Subgroup (D × (T ⧸ terminalTwoResidual T)) //
      J.map (MonoidHom.snd D (T ⧸ terminalTwoResidual T)) = ⊤ ∧
      P (J.map (MonoidHom.fst D (T ⧸ terminalTwoResidual T)))} :=
  Nat.card_congr (terminalContractionEquiv hD P)

/-- Concrete critical products satisfy the binary premise by actual fourth
powers, including all couplings in their projected subgroups. -/
theorem criticalProduct_isPGroup {ι : Type*} [Fintype ι] (a : ℕ) (d : ι → Bool) :
    IsPGroup 2 (CriticalProductGroup a d) := fun g => ⟨2,criticalProduct_pow_four a d g⟩

end SymmetricSubgroupAsymptotics
