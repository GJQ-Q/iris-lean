import LeanIrisX.Algebra.UpdateP

/-!
The public authoritative camera derived from View. Clients use this module
without depending on the internal `DFrac × Agreement` representation.
-/

namespace LeanIrisX

abbrev Auth (A : Type u) [OFE A] [CMRA A] [UCMRA A] :=
  View (AuthViewRel (A := A))

namespace Auth

variable {A : Type u} [OFE A] [CMRA A] [UCMRA A]

def authoritativeDFrac (dq : DFrac) (a : A) : Auth A :=
  View.Auth (R := AuthViewRel (A := A)) dq a

def authoritative (a : A) : Auth A :=
  View.FullAuth (R := AuthViewRel (A := A)) a

def fragment (b : A) : Auth A :=
  View.Frag (R := AuthViewRel (A := A)) b

theorem authoritative_fragment_validN {n : Nat} {a b : A} :
    CMRA.validN n (CMRA.op (authoritative a) (fragment b)) ↔
      CMRA.validN n a ∧ CMRA.IncludedN n b a := by
  exact View.auth_one_frag_validN_iff n a b

theorem authoritativeDFrac_fragment_validN {n : Nat} {dq : DFrac} {a b : A} :
    CMRA.validN n (CMRA.op (authoritativeDFrac dq a) (fragment b)) ↔
      CMRA.validN n dq ∧ CMRA.validN n a ∧ CMRA.IncludedN n b a := by
  exact View.auth_frag_validN_iff n dq a b

theorem authority_validN {n : Nat} {a b : A}
    (h : CMRA.validN n (CMRA.op (authoritative a) (fragment b))) :
    CMRA.validN n a :=
  (authoritative_fragment_validN.mp h).1

theorem fragment_includedN {n : Nat} {a b : A}
    (h : CMRA.validN n (CMRA.op (authoritative a) (fragment b))) :
    CMRA.IncludedN n b a :=
  (authoritative_fragment_validN.mp h).2

theorem fragment_validN {n : Nat} {a b : A}
    (h : CMRA.validN n (CMRA.op (authoritative a) (fragment b))) :
    CMRA.validN n b :=
  CMRA.validN_of_includedN (fragment_includedN h) (authority_validN h)

theorem authoritative_fragment_update {a a' b b' : A}
    (hup : ∀ n frame,
      AuthViewRel n a (CMRA.op b frame) →
      AuthViewRel n a' (CMRA.op b' frame)) :
    CMRA.FramePreservingUpdate
      (CMRA.op (authoritative a) (fragment b))
      (CMRA.op (authoritative a') (fragment b')) :=
  View.full_auth_frag_update hup

theorem authoritative_update {a a' : A}
    (hup : ∀ n frame, AuthViewRel n a frame → AuthViewRel n a' frame) :
    CMRA.FramePreservingUpdate (authoritative a) (authoritative a') :=
  View.full_auth_update hup

theorem alloc_fragment {a a' b : A}
    (hup : ∀ n frame, AuthViewRel n a frame →
      AuthViewRel n a' (CMRA.op b frame)) :
    CMRA.FramePreservingUpdate
      (authoritative a)
      (CMRA.op (authoritative a') (fragment b)) :=
  View.full_auth_alloc hup

theorem dealloc_fragment {a a' b : A}
    (hup : ∀ n frame, AuthViewRel n a (CMRA.op b frame) →
      AuthViewRel n a' frame) :
    CMRA.FramePreservingUpdate
      (CMRA.op (authoritative a) (fragment b))
      (authoritative a') :=
  View.full_auth_dealloc hup

/-- Predicate-valued authority/fragment update. -/
theorem authoritative_fragment_updateP {a b : A} (P : A → A → Prop)
    (hup : ∀ n frame, AuthViewRel n a (CMRA.op b frame) →
      ∃ a' b', P a' b' ∧ AuthViewRel n a' (CMRA.op b' frame)) :
    CMRA.FramePreservingUpdateP
      (CMRA.op (authoritative a) (fragment b))
      (fun target => ∃ a' b', P a' b' ∧
        target = CMRA.op (authoritative a') (fragment b')) :=
  View.full_auth_frag_updateP P hup

end Auth
end LeanIrisX
