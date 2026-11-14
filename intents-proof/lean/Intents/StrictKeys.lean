/-
  Who can change the public keys of an account in the strict world (`Intents/Strict.lean`).

  * `T4_key_power`   a key becomes a key of `u` only by `u`'s own `add_public_key` (with
                     authentication by predecessor enabled) or by an `AddPublicKey` intent of a
                     payload signed with a key already registered for `u`
-/
import Intents.StrictTheorems

namespace Intents
open ProvedFT

theorem contains_filter_ne {l : List Acct} {a u : Acct} (h : u ≠ a) :
    (l.filter fun x => x != a).contains u = l.contains u := by
  induction l with
  | nil => rfl
  | cons b t ih =>
    simp only [List.filter_cons]
    split
    · simp only [List.contains_cons, ih]
    · rename_i hb
      have hba : b = a := by simpa using hb
      subst hba
      have hub : (u == b) = false := by simpa using h
      simp only [List.contains_cons, ih, hub, Bool.false_or]

theorem bool_keys1 {x x0 e y : Bool} (h0 : ((!x0 && e) || y) = false)
    (h1 : ((!x && e) || y) = true) : e = true := by
  revert h0 h1; cases x <;> cases x0 <;> cases e <;> cases y <;> decide

theorem bool_keys2 {p b y : Bool} (h0 : (p || y) = false) (h1 : (p || (b || y)) = true) :
    b = true := by
  revert h0 h1; cases p <;> cases b <;> cases y <;> decide

theorem bool_keys3 {d x e y : Bool} (h1 : ((!(d || x) && e) || y) = true) :
    ((!x && e) || y) = true := by
  revert h1; cases d <;> cases x <;> cases e <;> cases y <;> decide

theorem bool_keys4 {p y y' : Bool} (hy : y' = true → y = true) (h1 : (p || y') = true) :
    (p || y) = true := by
  revert hy h1; cases p <;> cases y <;> cases y' <;> simp

/-- A successful `add_public_key(k')` for `a` makes `k` a key of `u` only if `u = a` and `k` is
    `k'` or has the same implicit account. -/
theorem addKey_has {implicit : Key → Acct} {c : Ctl} {A A' : AuthSt} {a u : Acct} {k' k : Key}
    (h : addKey implicit c A a k' = some A') (h0 : hasKey implicit A u k = false)
    (h1 : hasKey implicit A' u k = true) :
    u = a ∧ (k' = k ∨ implicit k' = implicit k) := by
  unfold addKey at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i hi
      have hia : implicit k' = a := by simpa using hi
      split at h
      · obtain rfl := Option.some.inj h
        by_cases hua : u = a
        · refine ⟨hua, Or.inr ?_⟩
          have he : (implicit k == u) = true := bool_keys1 h0 h1
          have hk : implicit k = u := by simpa using he
          rw [hia, hk, hua]
        · exfalso
          unfold hasKey at h0 h1
          have e := contains_filter_ne (l := A.noImplicit) hua
          simp only [e] at h1
          rw [h0] at h1; cases h1
      · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · obtain rfl := Option.some.inj h
        have hb : ((u, k) == (a, k')) = true := by
          unfold hasKey at h0 h1
          simp only [List.contains_cons] at h1
          exact bool_keys2 h0 h1
        have hp : (u, k) = (a, k') := by simpa using hb
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
        exact ⟨rfl, Or.inl rfl⟩

/-- A successful `remove_public_key` makes nothing a key. -/
theorem removeKey_has {implicit : Key → Acct} {c : Ctl} {A A' : AuthSt} {a u : Acct} {k' k : Key}
    (h : removeKey implicit c A a k' = some A') (h1 : hasKey implicit A' u k = true) :
    hasKey implicit A u k = true := by
  unfold removeKey at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · split at h
      · exact absurd h (by simp)
      · obtain rfl := Option.some.inj h
        unfold hasKey at h1 ⊢
        simp only [List.contains_cons] at h1
        exact bool_keys3 h1
    · split at h
      · obtain rfl := Option.some.inj h
        unfold hasKey at h1 ⊢
        exact bool_keys4 (fun hy => contains_of_filter hy) h1
      · exact absurd h (by simp)

theorem runOp_keys (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) (S S' : SWorld) (o : Op)
    (u : Acct) (k : Key) (h : runOp G ex signer S o = some S')
    (h1 : hasKey G.implicit S'.auth u k = true) :
    hasKey G.implicit S.auth u k = true ∨
    (u = signer ∧ ∃ k', o = .addKey k' ∧ (k' = k ∨ G.implicit k' = G.implicit k)) := by
  cases o with
  | withdraw w =>
    simp only [runOp] at h
    split at h
    · obtain rfl := Option.some.inj h; exact Or.inl h1
    · exact absurd h (by simp)
  | move dst amt call =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h; exact Or.inl h1
  | addKey k' =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i A ha
      obtain rfl := Option.some.inj h
      cases hb : hasKey G.implicit S.auth u k with
      | true => exact Or.inl rfl
      | false =>
        obtain ⟨hu, hk⟩ := addKey_has ha hb h1
        exact Or.inr ⟨hu, k', rfl, hk⟩
  | removeKey k' =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · rename_i A ha
      obtain rfl := Option.some.inj h
      exact Or.inl (removeKey_has ha h1)
  | setAuth en =>
    simp only [runOp] at h
    split at h
    · exact absurd h (by simp)
    · obtain rfl := Option.some.inj h; exact Or.inl h1

theorem runOps_keys (G : SCfg) (ex : St → Rcpt → Option Out) (signer : Acct) (u : Acct) (k : Key) :
    ∀ (ops : List Op) (S S' : SWorld), runOps G ex signer S ops = some S' →
      hasKey G.implicit S'.auth u k = true →
      hasKey G.implicit S.auth u k = true ∨
      (u = signer ∧ ∃ k', Op.addKey k' ∈ ops ∧ (k' = k ∨ G.implicit k' = G.implicit k)) := by
  intro ops
  induction ops with
  | nil =>
    intro S S' h h1
    have e : S = S' := by simpa [runOps] using h
    subst e
    exact Or.inl h1
  | cons o t ih =>
    intro S S' h h1
    simp only [runOps] at h
    split at h
    · exact absurd h (by simp)
    · rename_i S1 hop
      rcases ih S1 S' h h1 with h2 | ⟨hu, k', hmem, hk⟩
      · rcases runOp_keys G ex signer S S1 o u k hop h2 with h3 | ⟨hu, k', rfl, hk⟩
        · exact Or.inl h3
        · exact Or.inr ⟨hu, k', List.mem_cons.mpr (Or.inl rfl), hk⟩
      · exact Or.inr ⟨hu, k', List.mem_cons_of_mem _ hmem, hk⟩

/-- **T4, who can make a key of an account.** If `k` is not a key of `u` before a step of the
    strict world and is one after it, the step is one of two:
    1. `add_public_key(k')` called by `u` itself, with authentication by predecessor enabled;
    2. one signed payload with signer `u` whose signature verifies under a key that is already
       registered for `u`, with an `AddPublicKey(k')` among its intents.
    In both, `k'` is `k`, or a key with the same implicit account as `k` (adding back the
    implicit key of an account restores every key that maps to that account). No step makes a
    key of `u` on behalf of anyone else. -/
theorem T4_key_power (G : SCfg) (S : SWorld) (st : SStep) (u : Acct) (k : Key)
    (h0 : hasKey G.implicit S.auth u k = false)
    (h1 : hasKey G.implicit (sstd G S st).auth u k = true) :
    (∃ k', st = .addKey u k' ∧ (k' = k ∨ G.implicit k' = G.implicit k) ∧
      S.w.L.ctl.authOff.contains u = false) ∨
    (∃ now p sig k', st = .payload now p sig ∧ p.signer = u ∧ G.valid p.key p sig = true ∧
      hasKey G.implicit S.auth u p.key = true ∧ Op.addKey k' ∈ p.ops ∧
      (k' = k ∨ G.implicit k' = G.implicit k)) := by
  cases st with
  | base st0 =>
    exfalso
    have e : (sstd G S (.base st0)).auth = S.auth := by simp only [sstd, sstep]; split <;> rfl
    rw [e] at h1; exact ff_tt h0 h1
  | transfer src dst amt call =>
    exfalso
    have e : (sstd G S (.transfer src dst amt call)).auth = S.auth := by
      simp only [sstd, sstep]
      split
      · split <;> rfl
      · rfl
    rw [e] at h1; exact ff_tt h0 h1
  | forceTransfer who src dst amt call =>
    exfalso
    have e : (sstd G S (.forceTransfer who src dst amt call)).auth = S.auth := by
      simp only [sstd, sstep]; split <;> rfl
    rw [e] at h1; exact ff_tt h0 h1
  | resolveTransfer j req =>
    exfalso
    have e : (sstd G S (.resolveTransfer j req)).auth = S.auth := by
      simp only [sstd, sstep]
      split
      · rfl
      · split <;> rfl
    rw [e] at h1; exact ff_tt h0 h1
  | resolveTransferFails j => exact ff_tt h0 h1
  | payload now p sig =>
    by_cases hg : G.valid p.key p sig = true ∧
        admit G.implicit G.base.me now S.w.L.ctl S.auth p = true
    · cases hr : runOps G (exec G.base.tok) p.signer { S with auth := commitNonce S.auth p }
          p.ops with
      | none =>
        have e : sstd G S (.payload now p sig) = S := by simp only [sstd, sstep, ifP hg, hr]
        rw [e] at h1; exact ff_tt h0 h1
      | some S' =>
        have e : sstd G S (.payload now p sig) = S' := by simp only [sstd, sstep, ifP hg, hr]
        rw [e] at h1
        rcases runOps_keys G (exec G.base.tok) p.signer u k p.ops _ S' hr h1 with h2 |
            ⟨hu, k', hmem, hk⟩
        · exact ff_tt h0 h2
        · right
          obtain ⟨hv, ha⟩ := hg
          obtain ⟨_, _, hkey, _, _⟩ := admit_spec ha
          subst hu
          exact ⟨now, p, sig, k', rfl, rfl, hv, hkey, hmem, hk⟩
    · have e : sstd G S (.payload now p sig) = S := by simp only [sstd, sstep, ifN hg]
      rw [e] at h1; exact ff_tt h0 h1
  | addKey a k' =>
    by_cases hoff : S.w.L.ctl.authOff.contains a = true
    · have e : sstd G S (.addKey a k') = S := by simp only [sstd, sstep, ifP hoff]
      rw [e] at h1; exact ff_tt h0 h1
    · cases ha : addKey G.implicit S.w.L.ctl S.auth a k' with
      | none =>
        have e : sstd G S (.addKey a k') = S := by simp only [sstd, sstep, ifN hoff, ha]
        rw [e] at h1; exact ff_tt h0 h1
      | some A =>
        have e : (sstd G S (.addKey a k')).auth = A := by simp only [sstd, sstep, ifN hoff, ha]
        rw [e] at h1
        obtain ⟨hu, hk⟩ := addKey_has ha h0 h1
        subst hu
        left
        exact ⟨k', rfl, hk, by simpa using hoff⟩
  | removeKey a k' =>
    by_cases hoff : S.w.L.ctl.authOff.contains a = true
    · have e : sstd G S (.removeKey a k') = S := by simp only [sstd, sstep, ifP hoff]
      rw [e] at h1; exact ff_tt h0 h1
    · cases ha : removeKey G.implicit S.w.L.ctl S.auth a k' with
      | none =>
        have e : sstd G S (.removeKey a k') = S := by simp only [sstd, sstep, ifN hoff, ha]
        rw [e] at h1; exact ff_tt h0 h1
      | some A =>
        have e : (sstd G S (.removeKey a k')).auth = A := by simp only [sstd, sstep, ifN hoff, ha]
        rw [e] at h1
        exact ff_tt h0 (removeKey_has ha h1)
  | acl c => exact ff_tt h0 h1

end Intents
