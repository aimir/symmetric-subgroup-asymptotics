import SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparseWords

/-! The SAME selected sparse word and all its powers commute with the
actual coefficient-field homomorphism. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparsePowers
open CFSGFFourNormCertificateSparseWords CFSGReeFFourFieldEightWordTemplates
open CFSGReeFFourFieldEightCertificateField

theorem wordEnd_pow_map_apply (K : Type) [Field K] [CharP K 2]
    (e : Element →+* K) (s : List Letter) (n : ℕ) (v : Fin 26 → Element) :
    (fun j => e ((wordEnd Element (RingHom.id Element) s ^ n) v j)) =
      (wordEnd K e s ^ n) (fun j => e (v j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    calc
      _ = wordEnd K e s
          (fun j => e ((wordEnd Element (RingHom.id Element) s ^ n) v j)) :=
        wordEnd_map_apply K e s _
      _ = _ := congrArg (wordEnd K e s) ih

end SymmetricSubgroupAsymptotics.CFSGFFourNormCertificateSparsePowers
