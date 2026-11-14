/-
  The `accounts` map of near-contract-standards 3.1.0 `FungibleToken`
  (`LookupMap<AccountId, Balance>`), as an association list.

  `get` returns the first entry with the key, `set` overwrites the first entry
  with the key (or appends a new one), `erase` removes the first entry with the
  key. With `Nodup` (no repeated keys, an invariant of every reachable state)
  this is exactly a finite map.
-/
namespace WNear

abbrev Acct := String
abbrev Accts := List (Acct × Nat)

def get : Accts → Acct → Option Nat
  | [], _ => none
  | (k, v) :: t, a => if k = a then some v else get t a

/-- `ft_balance_of`: the balance, 0 for an unregistered account. -/
def bal (l : Accts) (a : Acct) : Nat := (get l a).getD 0

def set : Accts → Acct → Nat → Accts
  | [], a, v => [(a, v)]
  | (k, w) :: t, a, v => if k = a then (k, v) :: t else (k, w) :: set t a v

def erase : Accts → Acct → Accts
  | [], _ => []
  | (k, w) :: t, a => if k = a then t else (k, w) :: erase t a

/-- Sum of all balances. -/
def total : Accts → Nat
  | [] => 0
  | (_, v) :: t => v + total t

/-- No key occurs twice. -/
def Nodup : Accts → Prop
  | [] => True
  | (k, _) :: t => get t k = none ∧ Nodup t

/-- Storage stake of the entries, `c k` per entry. -/
def stor (c : Acct → Nat) : Accts → Nat
  | [] => 0
  | (k, _) :: t => c k + stor c t

theorem bal_of_some {l : Accts} {a : Acct} {v : Nat} (h : get l a = some v) : bal l a = v := by
  simp [bal, h]

theorem bal_of_none {l : Accts} {a : Acct} (h : get l a = none) : bal l a = 0 := by
  simp [bal, h]

theorem get_set (l : Accts) (a b : Acct) (v : Nat) :
    get (set l a v) b = if a = b then some v else get l b := by
  induction l with
  | nil => simp [set, get]
  | cons hd t ih =>
    obtain ⟨k, w⟩ := hd
    by_cases hka : k = a
    · subst hka
      by_cases hkb : k = b
      · subst hkb; simp [set, get]
      · simp [set, get, hkb]
    · by_cases hkb : k = b
      · subst hkb; simp [set, get, hka, Ne.symm hka]
      · simp [set, get, hka, hkb, ih]

theorem get_set_self (l : Accts) (a : Acct) (v : Nat) : get (set l a v) a = some v := by
  simp [get_set]

theorem get_set_ne (l : Accts) {a b : Acct} (v : Nat) (h : a ≠ b) :
    get (set l a v) b = get l b := by
  simp [get_set, h]

theorem bal_set_self (l : Accts) (a : Acct) (v : Nat) : bal (set l a v) a = v := by
  simp [bal, get_set_self]

theorem bal_set_ne (l : Accts) {a b : Acct} (v : Nat) (h : a ≠ b) :
    bal (set l a v) b = bal l b := by
  simp [bal, get_set_ne l v h]

theorem get_erase_ne (l : Accts) {a b : Acct} (h : a ≠ b) : get (erase l a) b = get l b := by
  induction l with
  | nil => simp [erase, get]
  | cons hd t ih =>
    obtain ⟨k, w⟩ := hd
    by_cases hka : k = a
    · subst hka; simp [erase, get, h]
    · by_cases hkb : k = b
      · subst hkb; simp [erase, get, hka]
      · simp [erase, get, hka, hkb, ih]

theorem bal_erase_ne (l : Accts) {a b : Acct} (h : a ≠ b) : bal (erase l a) b = bal l b := by
  simp [bal, get_erase_ne l h]

theorem get_erase_self {l : Accts} (hn : Nodup l) (a : Acct) : get (erase l a) a = none := by
  induction l with
  | nil => simp [erase, get]
  | cons hd t ih =>
    obtain ⟨k, w⟩ := hd
    obtain ⟨h1, h2⟩ := hn
    by_cases hka : k = a
    · subst hka; simp [erase, h1]
    · simp [erase, get, hka, ih h2]

theorem nodup_set {l : Accts} (hn : Nodup l) (a : Acct) (v : Nat) : Nodup (set l a v) := by
  induction l with
  | nil => simp [set, Nodup, get]
  | cons hd t ih =>
    obtain ⟨k, w⟩ := hd
    obtain ⟨h1, h2⟩ := hn
    by_cases hka : k = a
    · subst hka; simp only [set, if_pos rfl]; exact ⟨h1, h2⟩
    · simp only [set, if_neg hka]
      exact ⟨by rw [get_set_ne t v (Ne.symm hka)]; exact h1, ih h2⟩

theorem nodup_erase {l : Accts} (hn : Nodup l) (a : Acct) : Nodup (erase l a) := by
  induction l with
  | nil => simp [erase, Nodup]
  | cons hd t ih =>
    obtain ⟨k, w⟩ := hd
    obtain ⟨h1, h2⟩ := hn
    by_cases hka : k = a
    · subst hka; simp only [erase, if_pos rfl]; exact h2
    · simp only [erase, if_neg hka]
      exact ⟨by rw [get_erase_ne t (Ne.symm hka)]; exact h1, ih h2⟩

theorem total_set (l : Accts) (a : Acct) (v : Nat) :
    total (set l a v) + bal l a = total l + v := by
  induction l with
  | nil => simp [set, total, bal, get]
  | cons hd t ih =>
    obtain ⟨k, w⟩ := hd
    by_cases hka : k = a
    · subst hka; simp [set, total, bal, get]; omega
    · simp only [set, if_neg hka, total]
      have : bal ((k, w) :: t) a = bal t a := by simp [bal, get, hka]
      rw [this]; omega

theorem total_erase (l : Accts) (a : Acct) : total (erase l a) + bal l a = total l := by
  induction l with
  | nil => simp [erase, total, bal, get]
  | cons hd t ih =>
    obtain ⟨k, w⟩ := hd
    by_cases hka : k = a
    · subst hka; simp [erase, total, bal, get]; omega
    · simp only [erase, if_neg hka, total]
      have : bal ((k, w) :: t) a = bal t a := by simp [bal, get, hka]
      rw [this]; omega

theorem bal_le_total (l : Accts) (a : Acct) : bal l a ≤ total l := by
  induction l with
  | nil => simp [bal, get]
  | cons hd t ih =>
    obtain ⟨k, w⟩ := hd
    by_cases hka : k = a
    · subst hka; simp [bal, get, total]
    · have : bal ((k, w) :: t) a = bal t a := by simp [bal, get, hka]
      rw [this]; simp only [total]; omega

theorem get_le_total {l : Accts} {a : Acct} {v : Nat} (h : get l a = some v) : v ≤ total l := by
  have := bal_le_total l a; rwa [bal_of_some h] at this

theorem length_pos_of_get {l : Accts} {a : Acct} {v : Nat} (h : get l a = some v) :
    0 < l.length := by
  cases l with
  | nil => simp [get] at h
  | cons hd t => simp

theorem length_set_some {l : Accts} {a : Acct} {w : Nat} (h : get l a = some w) (v : Nat) :
    (set l a v).length = l.length := by
  induction l with
  | nil => simp [get] at h
  | cons hd t ih =>
    obtain ⟨k, x⟩ := hd
    by_cases hka : k = a
    · subst hka; simp [set]
    · simp only [get, if_neg hka] at h
      simp [set, hka, ih h]

theorem length_set_none {l : Accts} {a : Acct} (h : get l a = none) (v : Nat) :
    (set l a v).length = l.length + 1 := by
  induction l with
  | nil => simp [set]
  | cons hd t ih =>
    obtain ⟨k, x⟩ := hd
    by_cases hka : k = a
    · subst hka; simp [get] at h
    · simp only [get, if_neg hka] at h
      simp [set, hka, ih h]

theorem length_erase_some {l : Accts} {a : Acct} {w : Nat} (h : get l a = some w) :
    (erase l a).length + 1 = l.length := by
  induction l with
  | nil => simp [get] at h
  | cons hd t ih =>
    obtain ⟨k, x⟩ := hd
    by_cases hka : k = a
    · subst hka; simp [erase]
    · simp only [get, if_neg hka] at h
      simp [erase, hka]; have := ih h; omega

theorem stor_set_some (c : Acct → Nat) {l : Accts} {a : Acct} {w : Nat} (h : get l a = some w)
    (v : Nat) : stor c (set l a v) = stor c l := by
  induction l with
  | nil => simp [get] at h
  | cons hd t ih =>
    obtain ⟨k, x⟩ := hd
    by_cases hka : k = a
    · subst hka; simp [set, stor]
    · simp only [get, if_neg hka] at h
      simp [set, hka, stor, ih h]

theorem stor_le (c : Acct → Nat) (m : Nat) (hc : ∀ a, c a ≤ m) (l : Accts) :
    stor c l ≤ l.length * m := by
  induction l with
  | nil => simp [stor]
  | cons hd t ih =>
    obtain ⟨k, x⟩ := hd
    simp only [stor, List.length_cons, Nat.add_mul, Nat.one_mul]
    have := hc k; omega

/-- If every entry costs at least `e` and `m ≤ 2 * e`, the per-account refunds
`length * m` are at most twice the stake of the entries. -/
theorem length_mul_le_stor (c : Acct → Nat) (m : Nat) (hc : ∀ a, m ≤ 2 * c a) (l : Accts) :
    l.length * m ≤ 2 * stor c l := by
  induction l with
  | nil => simp
  | cons hd t ih =>
    obtain ⟨k, x⟩ := hd
    simp only [stor, List.length_cons, Nat.add_mul, Nat.one_mul]
    have := hc k; omega

end WNear
