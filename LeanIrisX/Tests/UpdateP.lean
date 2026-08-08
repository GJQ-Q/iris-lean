import LeanIrisX.Algebra.Auth

namespace LeanIrisX.Tests.UpdateP

open LeanIrisX

theorem auth_unit_predicate_update :
    CMRA.FramePreservingUpdateP
      (CMRA.op (Auth.authoritative ()) (Auth.fragment ()))
      (fun target : Auth Unit => ∃ a' b' : Unit,
        (a' = () ∧ b' = ()) ∧
        target = CMRA.op (Auth.authoritative a') (Auth.fragment b')) := by
  apply Auth.authoritative_fragment_updateP (fun a' b' : Unit => a' = () ∧ b' = ())
  intro n frame h
  exact ⟨(), (), ⟨rfl, rfl⟩, h⟩

theorem deterministic_embeds_into_predicate_update :
    CMRA.FramePreservingUpdateP
      (Auth.authoritative ()) (fun target : Auth Unit => target = Auth.authoritative ()) := by
  apply CMRA.update_to_updateP
  apply Auth.authoritative_update
  intro n frame h
  exact h

end LeanIrisX.Tests.UpdateP
