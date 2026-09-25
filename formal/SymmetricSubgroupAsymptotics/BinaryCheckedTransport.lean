import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-!
# Literal checked permutation carriers with untouched exterior

The carrier is a literal subgroup on the same physical set. Its auxiliary
quotient degree is separate. Both epimorphisms and both original kernels
are retained; transport recovers every exterior correlation.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

structure CheckedPermutationCarrier (w q : ℕ) where
  source : Subgroup (Equiv.Perm (Fin w))
  carrier : Subgroup (Equiv.Perm (Fin w))
  quotient : Subgroup (Equiv.Perm (Fin q))
  axis : Subgroup (Equiv.Perm (Fin w))
  carrierKernel : Subgroup (Equiv.Perm (Fin w))
  alpha : source →* quotient
  beta : carrier →* quotient
  alpha_surjective : Function.Surjective alpha
  beta_surjective : Function.Surjective beta
  alpha_kernel : alpha.ker.map source.subtype = axis
  beta_kernel : beta.ker.map carrier.subtype = carrierKernel

namespace CheckedPermutationCarrier

/-- Install two literal finite graph certificates as a carrier chart. The
range and kernel equations are proved from rows in each application. -/
def ofCertificates {w q n m : ℕ} {ι κ : Type*}
    {s : ι → Equiv.Perm (Fin w)} {si : ι → Equiv.Perm (Fin q)}
    {t : κ → Equiv.Perm (Fin w)} {ti : κ → Equiv.Perm (Fin q)}
    (C : FiniteHomCertificate s si n) (D : FiniteHomCertificate t ti m)
    (Q : Subgroup (Equiv.Perm (Fin q)))
    (K L : Subgroup (Equiv.Perm (Fin w)))
    (hC : C.hom.range = Q) (hD : D.hom.range = Q)
    (hK : C.hom.ker.map (Subgroup.closure (Set.range s)).subtype = K)
    (hL : D.hom.ker.map (Subgroup.closure (Set.range t)).subtype = L) :
    CheckedPermutationCarrier w q where
  source := Subgroup.closure (Set.range s)
  carrier := Subgroup.closure (Set.range t)
  quotient := Q
  axis := K
  carrierKernel := L
  alpha := C.hom.codRestrict Q (fun x => hC ▸ ⟨x, rfl⟩)
  beta := D.hom.codRestrict Q (fun x => hD ▸ ⟨x, rfl⟩)
  alpha_surjective := by
    rintro ⟨y, hy⟩
    rw [← hC] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  beta_surjective := by
    rintro ⟨y, hy⟩
    rw [← hD] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  alpha_kernel := by simpa only [MonoidHom.ker_codRestrict] using hK
  beta_kernel := by simpa only [MonoidHom.ker_codRestrict] using hL

variable {w q : ℕ} (C : CheckedPermutationCarrier w q)
    {E : Type*} [Group E]

def sourceMap : C.source × E →* C.quotient × E :=
  C.alpha.prodMap (MonoidHom.id E)

def carrierMap : C.carrier × E →* C.quotient × E :=
  C.beta.prodMap (MonoidHom.id E)

theorem sourceMap_surjective : Function.Surjective (C.sourceMap (E := E)) := by
  rintro ⟨y,e⟩
  obtain ⟨x,hx⟩ := C.alpha_surjective y
  exact ⟨(x,e),Prod.ext hx rfl⟩

theorem carrierMap_surjective : Function.Surjective (C.carrierMap (E := E)) := by
  rintro ⟨y,e⟩
  obtain ⟨x,hx⟩ := C.beta_surjective y
  exact ⟨(x,e),Prod.ext hx rfl⟩

def transport (H : Subgroup (C.source × E)) : Subgroup (C.carrier × E) :=
  (H.map C.sourceMap).comap C.carrierMap

/-- The original axis condition contains exactly the source map kernel.
The exterior group is arbitrary and may be nonabelian. -/
theorem sourceMap_kernel_le (H : Subgroup (C.source × E))
    (haxis : ∀ x : C.source, (x : Equiv.Perm (Fin w)) ∈ C.axis → (x,1) ∈ H) :
    (C.sourceMap (E := E)).ker ≤ H := by
  rintro ⟨x,e⟩ hx
  have he : e = 1 := congrArg Prod.snd hx
  have ha : C.alpha x = 1 := congrArg Prod.fst hx
  rw [he]
  apply haxis x
  rw [← C.alpha_kernel]
  exact ⟨x,ha,rfl⟩

/-- The whole original subgroup, including every exterior correlation,
is recovered by the two original quotient maps. -/
theorem transport_reconstruct (H : Subgroup (C.source × E))
    (haxis : ∀ x : C.source, (x : Equiv.Perm (Fin w)) ∈ C.axis → (x,1) ∈ H) :
    ((C.transport H).map C.carrierMap).comap C.sourceMap = H := by
  rw [transport, Subgroup.map_comap_eq_self_of_surjective C.carrierMap_surjective,
    Subgroup.comap_map_eq_self (C.sourceMap_kernel_le H haxis)]

/-- Even the literal exterior image is unchanged, rather than merely
being replaced by an isomorphic or larger subgroup. -/
theorem transport_exterior (H : Subgroup (C.source × E)) :
    (C.transport H).map (MonoidHom.snd C.carrier E) =
      H.map (MonoidHom.snd C.source E) := by
  apply le_antisymm
  · rintro e ⟨⟨x,e'⟩,hx,rfl⟩
    obtain ⟨⟨y,f⟩,hy,he⟩ := hx
    have hf : f = e' := congrArg Prod.snd he
    exact ⟨(y,f),hy,hf⟩
  · rintro e ⟨⟨x,e'⟩,hx,rfl⟩
    obtain ⟨y,hy⟩ := C.beta_surjective (C.alpha x)
    refine ⟨(y,e'),?_,rfl⟩
    exact ⟨(x,e'),hx,Prod.ext hy.symm rfl⟩

/-- Fullness of the source projection gives fullness on the entire
literal proper carrier, not just each of its displayed projections. -/
theorem transport_full_carrier (H : Subgroup (C.source × E))
    (hfull : ∀ x : C.source, ∃ e : E, (x,e) ∈ H) :
    ∀ y : C.carrier, ∃ e : E, (y,e) ∈ C.transport H := by
  intro y
  obtain ⟨x,hx⟩ := C.alpha_surjective (C.beta y)
  obtain ⟨e,he⟩ := hfull x
  exact ⟨e,⟨(x,e),he,Prod.ext hx rfl⟩⟩

theorem transport_injective : Function.Injective
    (fun H : {H : Subgroup (C.source × E) //
      ∀ x : C.source, (x : Equiv.Perm (Fin w)) ∈ C.axis → (x,1) ∈ H} =>
      C.transport H.1) := by
  intro H K he
  apply Subtype.ext
  have hh := congrArg (fun L : Subgroup (C.carrier × E) =>
    (L.map C.carrierMap).comap C.sourceMap) he
  simpa only [C.transport_reconstruct H.1 H.2,C.transport_reconstruct K.1 K.2] using hh

end CheckedPermutationCarrier

end SymmetricSubgroupAsymptotics
