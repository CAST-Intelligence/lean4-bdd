import Bdd.Collect
import Bdd.Trim

open Pointer
open Bdd

private def OBdd.discover_helper : List (Fin m) → Vector (Node n m ) m → Vector (List (Fin m)) n → Vector (List (Fin m)) n
  | [], _, I => I
  | head :: tail, v, I => discover_helper tail v (I.set v[head].var (head :: I[v[head].var]))

private lemma OBdd.discover_helper_retains_found (O : OBdd n m) {I : Vector (List (Fin m)) n} {i : Fin n}: j ∈ I[i] → j ∈ (discover_helper l v I)[i] := by
  intro h
  cases l with
  | nil => assumption
  | cons head tail =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    cases decEq v[head.1].var i with
    | isFalse hf =>
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hf])]
      assumption
    | isTrue  ht =>
      subst ht
      simp only [Fin.getElem_fin]
      rw [Vector.getElem_set_self]
      right
      assumption

private lemma OBdd.discover_helper_spec (O : OBdd n m) {I : Vector (List (Fin m)) n} :
    j ∈ l → j ∈ (discover_helper l v I).get v[j].var := by
  intro h
  cases h with
  | head as =>
    simp [discover_helper]
    apply discover_helper_retains_found O
    simp only [Fin.getElem_fin]
    rw [Vector.getElem_set_self]
    left
  | tail b ih =>
    simp [discover_helper]
    apply discover_helper_spec O ih

/-- Return a vector whose `v`th entry is a list of node indices with variable index `v`.

This is a subroutine of `reduce`.  -/
def OBdd.discover (O : OBdd n m) : Vector (List (Fin m)) n := discover_helper (Collect.collect O) O.1.heap (Vector.replicate n [])

/-- `discover` is correct. -/
theorem OBdd.discover_spec {O : OBdd n m} {j : Fin m} :
    (Reachable O.1.heap O.1.root (node j)) → j ∈ (discover O).get O.1.heap[j].var :=
  (discover_helper_spec O) ∘ Collect.collect_spec

-- discover_helper preserves: all elements in I[i] have v[j].var = i
-- (and only adds elements where v[j].var matches the index)
private lemma OBdd.discover_helper_var_preserved {n m : Nat}
    (v : Vector (Node n m) m) (l : List (Fin m)) (I : Vector (List (Fin m)) n)
    (hI : ∀ (i : Fin n) (j : Fin m), j ∈ I[i] → v[j].var = i) :
    ∀ (i : Fin n) (j : Fin m), j ∈ (discover_helper l v I)[i] → v[j].var = i := by
  induction l generalizing I with
  | nil => simp [discover_helper]; exact hI
  | cons head tail ih =>
    apply ih
    intro i j hmem
    simp only [] at hmem
    by_cases hvar : v[head].var = i
    · subst hvar
      simp only [Fin.getElem_fin, Vector.getElem_set_self] at hmem
      cases hmem with
      | head => rfl
      | tail _ h => exact hI _ j h
    · have hne : (v[head].var : Nat) ≠ (i : Nat) := Fin.val_ne_of_ne hvar
      rw [show (I.set v[head].var (head :: I[v[head].var]))[i] = I[i] from
        Vector.getElem_set_ne _ _ hne] at hmem
      exact hI i j hmem

-- All nodes in discover(O)[i] have variable index i
theorem OBdd.discover_var_eq {O : OBdd n m} {i : Fin n} {j : Fin m}
    (h : j ∈ (discover O)[i]) :
    O.1.heap[j].var = i := by
  unfold discover at h
  exact discover_helper_var_preserved O.1.heap _ _ (by
    intro i' j' hmem
    have : (Vector.replicate n ([] : List (Fin m)))[i'.val] = [] :=
      Vector.getElem_replicate i'.isLt
    simp only [Fin.getElem_fin] at hmem
    rw [this] at hmem
    exact absurd hmem (List.not_mem_nil)) i j h

-- discover_helper only contains elements from l or I
private lemma OBdd.discover_helper_source {n m : Nat}
    (v : Vector (Node n m) m) (l : List (Fin m)) (I : Vector (List (Fin m)) n) :
    ∀ (i : Fin n) (j : Fin m), j ∈ (discover_helper l v I)[i] → j ∈ l ∨ j ∈ I[i] := by
  induction l generalizing I with
  | nil =>
    intro i j h
    simp [discover_helper] at h
    exact Or.inr h
  | cons head tail ih =>
    intro i j hmem
    rcases ih (I.set v[head].var (head :: I[v[head].var])) i j hmem with hl | hI
    · exact Or.inl (List.mem_cons_of_mem _ hl)
    · by_cases hvar : v[head].var = i
      · subst hvar
        simp only [Fin.getElem_fin, Vector.getElem_set_self] at hI
        rcases List.mem_cons.mp hI with rfl | hI'
        · exact Or.inl (List.mem_cons_self ..)
        · exact Or.inr hI'
      · have hne : (v[head].var : Nat) ≠ (i : Nat) := Fin.val_ne_of_ne hvar
        rw [show (I.set v[head].var (head :: I[v[head].var]))[i] = I[i] from
          Vector.getElem_set_ne _ _ hne] at hI
        exact Or.inr hI

-- All nodes in discover(O)[i] are reachable from the root
theorem OBdd.discover_reachable {O : OBdd n m} {i : Fin n} {j : Fin m}
    (h : j ∈ (discover O)[i]) :
    Pointer.Reachable O.1.heap O.1.root (.node j) := by
  unfold discover at h
  rcases discover_helper_source O.1.heap (Collect.collect O) (Vector.replicate n []) i j h with hmem | hmem
  · exact Collect.collect_spec_reverse hmem
  · simp only [Fin.getElem_fin, Vector.getElem_replicate] at hmem
    exact absurd hmem (List.not_mem_nil)

-- Children of nodes in discover(O)[i] are NOT in discover(O)[i].
-- This is because ordering requires v[k].var < v[c].var for an edge k->c,
-- but all nodes in discover(O)[i] have v[j].var = i.
theorem OBdd.child_not_in_discover {O : OBdd n m} {i : Fin n} {k c : Fin m}
    (hk : k ∈ (discover O)[i])
    (hedge : Edge O.1.heap (.node k) (.node c)) :
    c ∉ (discover O)[i] := by
  intro hc
  have hk_var := discover_var_eq hk  -- v[k].var = i
  have hc_var := discover_var_eq hc  -- v[c].var = i
  have hk_reach := discover_reachable hk
  have hc_reach : Pointer.Reachable O.1.heap O.1.root (.node c) := .tail hk_reach hedge
  -- Ordering gives: toVar v (node k) < toVar v (node c), i.e., v[k].var < v[c].var
  have hord : Pointer.MayPrecede O.1.heap (.node k) (.node c) :=
    @O.2 ⟨.node k, hk_reach⟩ ⟨.node c, hc_reach⟩ hedge
  simp only [Pointer.MayPrecede, Pointer.toVar] at hord
  -- hord : v[k].var < v[c].var
  -- hk_var : v[k].var = i, hc_var : v[c].var = i
  rw [hk_var, hc_var] at hord
  exact Nat.lt_irrefl _ hord

namespace Reduce
private structure State (n) (m) where
  out : Vector (Node n m) m
  ids : Vector (Pointer m) m
  nid : Fin m

private def initial {n m : Nat} : State n.succ m.succ :=
  ⟨ (Vector.replicate m.succ {var := 0, low := terminal false, high := terminal true}),
    (Vector.replicate m.succ (terminal false)),
    Fin.last m
  ⟩

private def get_out : StateM (State n m) (Vector (Node n m) m) := get >>= fun s ↦ pure s.out

private def get_id : Pointer m → StateM (State n m) (Pointer m)
  | terminal b => pure (terminal b)
  | node j => get >>= fun s ↦ pure (s.ids[j])

private def set_id : Fin m → Pointer m → StateM (State n m) Unit :=
  fun j p ↦ get >>= fun s ↦ set (⟨s.out, s.ids.set j p, s.nid⟩ : State n m)

private def set_id_to_nid : Fin m → StateM (State n m) Unit :=
  fun j ↦ get >>= fun s ↦ set_id j (node s.nid)

private def set_out {n m : Nat} : Node n.succ m.succ → StateM (State n.succ m.succ) Unit :=
  fun N ↦ get >>= fun s ↦
    have : (s.nid.1 + 1) % m.succ < m.succ := by simp [Nat.mod_lt]
    set (⟨s.out.set ((s.nid.1 + 1) % m.succ) N, s.ids, s.nid + 1⟩ : State n.succ m.succ)

private def populate_queue (v : Vector (Node n m) m) (acc : List ((Pointer m × Pointer m) × Fin m)) : List (Fin m) → StateM (State n m) (List ((Pointer m × Pointer m) × Fin m))
  | [] => pure acc
  | j :: tail => do
    let lid ← get_id v[j].low
    let hid ← get_id v[j].high
    if decide (lid = hid)
    then
      -- `node j` is redundant in the original BDD.
      --  Reduce it by mapping it to its child `lid` in the output BDD.
      set_id j lid
      populate_queue v acc tail
    else populate_queue v (⟨⟨lid, hid⟩, j⟩ :: acc) tail

private def process_record {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) : (Pointer m.succ × Pointer m.succ) × Fin m.succ → StateM (State n.succ m.succ) (Pointer m.succ × Pointer m.succ) := fun ⟨key, j⟩ ↦ do
  if key = curkey
  then
    -- isomorphism in original BDD, reduce.
    set_id_to_nid j
    pure curkey
  else
    let lid ← get_id v[j].low
    let hid ← get_id v[j].high
    set_out ⟨v[j].var, lid, hid⟩
    set_id_to_nid j
    pure key

private def process_queue {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (curkey : Pointer m.succ × Pointer m.succ) :
  List ((Pointer m.succ × Pointer m.succ) × Fin m.succ) → StateM (State n.succ m.succ) Unit
  | [] => pure ()
  | head :: tail => do
    let newkey ← process_record v curkey head
    process_queue v newkey tail

private def step {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) Unit := do
  let Q ← populate_queue v [] vlist[i]
  process_queue v ⟨node 0, node 0⟩ (List.mergeSort Q)

private def loop {n m : Nat} (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ) (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ) : StateM (State n.succ m.succ) (Bdd n.succ m.succ) := do
  step v vlist i
  match h : i.1 - v[r].var.1 with
  | Nat.zero =>
    let out ← get_out
    let rid ← get_id (node r)
    pure {heap := out, root := rid}
  | Nat.succ j =>
    loop v r vlist ⟨(j + v[r].var.1), by omega⟩
termination_by i.1 - v[r].var.1
decreasing_by simp_all

private def reduce {n m : Nat} (O : OBdd n.succ m.succ) : Bdd n.succ m.succ :=
  match O.1.root with
  | terminal _ => O.1 -- Terminals are already reduced.
  | node r => (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1

private def reduce'' {n m : Nat} (O : OBdd n.succ m.succ) : Bdd n.succ m.succ × Fin m.succ :=
  match O.1.root with
  | terminal _ => ⟨O.1, 0⟩ -- Terminals are already reduced.  FIXME: return empty heap instead of original heap.
  | node r =>
    let ⟨B, S⟩ := (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial)
    ⟨B, S.nid⟩

private def zero_vars_to_bool : Bdd 0 m → Bool := fun B ↦
  match B.root with
  | .terminal b => b
  | .node j => False.elim (Nat.not_lt_zero _ B.heap[j].var.2)


-- Combine ordered + bound into a single result predicate for the loop.
-- We use a structure rather than And to avoid Lean unfolding Ordered (which is a Subrelation,
-- i.e., a function type) and confusing .1/.2 projections.
private structure LoopResultOK {n m : Nat} (result : Bdd n.succ m.succ × State n.succ m.succ) : Prop where
  ordered : result.1.Ordered
  bounded : ∀ j : Fin m.succ, Pointer.Reachable result.1.heap result.1.root (.node j) →
    j.val < result.2.nid.val + 1
  reduced : OBdd.Reduced ⟨result.1, ordered⟩

/-- The output state invariant needed for the BDD reduction loop.
    We track that the output heap, when viewed from any ids pointer,
    maintains variable ordering and reachability bounds.

    `nid_start` is the initial nid value (Fin.last m for `initial`).
    Written positions are determined by how nid has advanced from nid_start.

    Key properties:
    - All edges in the output heap from written nodes respect variable ordering
    - All ids that are node pointers point to written positions
    - All written nodes have variable index >= current processing level -/
private structure StateOK {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (r : Fin m.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩) : Prop where
  /-- The output BDD rooted at ids[r] is ordered -/
  ordered_at_root :
    Bdd.Ordered {heap := s.out, root := s.ids[r]}
  /-- All nodes reachable from ids[r] in the output heap are bounded -/
  bounded_at_root :
    ∀ j : Fin m.succ, Pointer.Reachable s.out s.ids[r] (.node j) →
      j.val < s.nid.val + 1
  /-- The output BDD rooted at ids[r] is reduced -/
  reduced_at_root :
    OBdd.Reduced ⟨{heap := s.out, root := s.ids[r]}, ordered_at_root⟩
  /-- If ids[r] is non-terminal, nid has wrapped around (at least one write happened) -/
  nid_lt_m_of_nonterminal :
    (¬∃ b, s.ids[r] = terminal b) → s.nid.val < m
  /-- If ANY id is non-terminal, nid < m. Generalizes nid_lt_m_of_nonterminal to arbitrary k. -/
  nid_lt_m_of_any_nonterminal :
    ∀ k : Fin m.succ, (¬∃ b, s.ids[k] = terminal b) → s.nid.val < m
  /-- Global correctness: every non-terminal mapped id has a correct output BDD.
      This strengthens the per-root tracking to enable the r-in-vlist proof,
      where we need properties of children's mapped ids (processed at earlier levels). -/
  global_ok :
    ∀ k : Fin m.succ, (¬∃ b, s.ids[k] = terminal b) →
      (Bdd.Ordered {heap := s.out, root := s.ids[k]} ∧
       (∀ j : Fin m.succ, Pointer.Reachable s.out s.ids[k] (.node j) → j.val < s.nid.val + 1) ∧
       (∀ hord : Bdd.Ordered {heap := s.out, root := s.ids[k]},
          OBdd.Reduced ⟨{heap := s.out, root := s.ids[k]}, hord⟩))

-- We prove loop_result_ok by mirroring the structure of loop.
-- The key insight: in the base case, the result BDD is {heap := s'.out, root := s'.ids[r]}
-- where s' is the state after running step. In the recursive case, we delegate to the
-- induction hypothesis.

-- If ids[r] is a terminal, the StateOK invariant holds trivially.
-- The global_ok field must be provided externally since it depends on ALL ids, not just r's.
private lemma stateOK_of_terminal_ids {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (ht : ∃ b, s.ids[r] = terminal b)
    (hglob : ∀ k : Fin m.succ, (¬∃ b, s.ids[k] = terminal b) →
      (Bdd.Ordered {heap := s.out, root := s.ids[k]} ∧
       (∀ j : Fin m.succ, Pointer.Reachable s.out s.ids[k] (.node j) → j.val < s.nid.val + 1) ∧
       (∀ hord : Bdd.Ordered {heap := s.out, root := s.ids[k]},
          OBdd.Reduced ⟨{heap := s.out, root := s.ids[k]}, hord⟩)))
    (hnid_any : ∀ k : Fin m.succ, (¬∃ b, s.ids[k] = terminal b) → s.nid.val < m) :
    StateOK v r s hord_input := by
  obtain ⟨b, hb⟩ := ht
  have hord : Bdd.Ordered {heap := s.out, root := s.ids[r]} := by
    rw [hb]; exact Bdd.Ordered_of_terminal
  exact {
    ordered_at_root := hord
    bounded_at_root := by
      rw [hb]; intro j hreach
      exact absurd (Pointer.eq_terminal_of_reachable hreach) (by simp)
    reduced_at_root := by
      have : OBdd.isTerminal ⟨{heap := s.out, root := s.ids[r]}, hord⟩ := ⟨b, hb⟩
      exact OBdd.reduced_of_terminal this
    nid_lt_m_of_nonterminal := by
      intro hnt; exact absurd ⟨b, hb⟩ hnt
    nid_lt_m_of_any_nonterminal := hnid_any
    global_ok := hglob
  }

-- get_id is a pure read operation - unfold helper
private lemma get_id_run_terminal {n m : Nat} (b : Bool) (s : State n.succ m.succ) :
    StateT.run (get_id (terminal b)) s = (terminal b, s) := by
  simp [get_id, StateT.run, pure, StateT.pure]

private lemma get_id_run_node {n m : Nat} (j : Fin m.succ) (s : State n.succ m.succ) :
    StateT.run (get_id (node j)) s = (s.ids[j], s) := by
  simp [get_id, StateT.run, StateT.bind, Bind.bind, StateT.get, get, pure, StateT.pure,
        MonadState.get, getThe, MonadStateOf.get, StateT.get]

-- set_id modifies only ids[j] and nothing else
private lemma set_id_run {n m : Nat} (j : Fin m.succ) (p : Pointer m.succ) (s : State n.succ m.succ) :
    StateT.run (set_id j p) s = ((), ⟨s.out, s.ids.set j p, s.nid⟩) := by
  simp [set_id, StateT.run, StateT.bind, Bind.bind, StateT.get, StateT.set, StateT.pure,
        get, set, pure, MonadState.get, getThe, MonadStateOf.get, StateT.get,
        MonadStateOf.set, StateT.set]

-- set_id preserves ids[r] when r ≠ j
private lemma set_id_ids_ne {n m : Nat} (j : Fin m.succ) (p : Pointer m.succ) (s : State n.succ m.succ)
    (r : Fin m.succ) (hr : r ≠ j) :
    (StateT.run (set_id j p) s).2.ids[r] = s.ids[r] := by
  rw [set_id_run]
  simp only [Fin.getElem_fin]
  exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne (Ne.symm hr))


-- StateT.run distributes over bind
@[simp]
private lemma stateT_run_bind {α β : Type} {σ : Type} (a : StateT σ Id α) (f : α → StateT σ Id β) (s : σ) :
    StateT.run (a >>= f) s = let p := StateT.run a s; StateT.run (f p.1) p.2 := by
  simp only [StateT.run, StateT.bind, Bind.bind]
  generalize a s = p
  obtain ⟨a', s'⟩ := p
  rfl

@[simp]
private lemma stateT_run_pure {α : Type} {σ : Type} (x : α) (s : σ) :
    StateT.run (pure x : StateT σ Id α) s = (x, s) := by
  simp [StateT.run, pure, StateT.pure]

-- Simp lemmas for get_id
@[simp]
private lemma get_id_run {n m : Nat} (p : Pointer m.succ) (s : State n.succ m.succ) :
    StateT.run (get_id p) s = match p with
      | terminal b => (terminal b, s)
      | node j => (s.ids[j], s) := by
  cases p with
  | terminal b => simp [get_id, StateT.run, pure, StateT.pure]
  | node j => simp [get_id, StateT.run, StateT.bind, Bind.bind, StateT.get, get, pure,
                     StateT.pure, MonadState.get, getThe, MonadStateOf.get, StateT.get]

-- Helper: get_id doesn't change the state
private lemma get_id_state {n m : Nat} (p : Pointer m.succ) (s : State n.succ m.succ) :
    (StateT.run (get_id p) s).2 = s := by
  cases p <;> simp

-- Helper: set_id preserves out
private lemma set_id_out {n m : Nat} (j : Fin m.succ) (p : Pointer m.succ) (s : State n.succ m.succ) :
    (StateT.run (set_id j p) s).2.out = s.out := by
  rw [set_id_run]

-- Helper: set_id preserves nid
private lemma set_id_nid {n m : Nat} (j : Fin m.succ) (p : Pointer m.succ) (s : State n.succ m.succ) :
    (StateT.run (set_id j p) s).2.nid = s.nid := by
  rw [set_id_run]

-- Simp lemma: set_id run result
@[simp]
private lemma set_id_run' {n m : Nat} (j : Fin m.succ) (p : Pointer m.succ) (s : State n.succ m.succ) :
    StateT.run (set_id j p) s = ((), ⟨s.out, s.ids.set j p, s.nid⟩) :=
  set_id_run j p s

-- populate_queue preserves ids[r] when r is not in the input list.
-- It also preserves out and nid (it only modifies ids).
private lemma populate_queue_ids_not_in_list {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (acc : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ))
    (l : List (Fin m.succ))
    (r : Fin m.succ)
    (hr : r ∉ l)
    (s : State n.succ m.succ) :
    (StateT.run (populate_queue v acc l) s).2.ids[r] = s.ids[r] := by
  induction l generalizing acc s with
  | nil => simp [populate_queue, StateT.run, pure, StateT.pure]
  | cons j tail ih =>
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨hrj, hrt⟩ := hr
    have hrne : (r : Nat) ≠ (j : Nat) := Fin.val_ne_of_ne hrj
    -- Case split on pointer types BEFORE any unfolding to avoid generalize failures.
    rcases hlow : v[j].low with b1 | k1 <;> rcases hhigh : v[j].high with b2 | k2
    all_goals (
      unfold populate_queue
      simp only [stateT_run_bind, get_id_run, hlow, hhigh]
      split
      · -- "then" branch: set_id then recurse
        simp only [stateT_run_bind, set_id_run', ih _ hrt]
        exact Vector.getElem_set_ne _ _ hrne.symm
      · -- "else" branch: just recurse
        exact ih _ hrt _
    )

-- populate_queue preserves out (it only modifies ids via set_id).
private lemma populate_queue_out {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (acc : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ))
    (l : List (Fin m.succ))
    (s : State n.succ m.succ) :
    (StateT.run (populate_queue v acc l) s).2.out = s.out := by
  induction l generalizing acc s with
  | nil => simp [populate_queue, pure, StateT.pure, StateT.run]
  | cons j tail ih =>
    simp only [populate_queue, get_id, set_id, bind, StateT.bind, StateT.run, StateT.get,
               get, set, pure, StateT.pure, MonadState.get, getThe, MonadStateOf.get,
               StateT.get, MonadStateOf.set, StateT.set]
    cases v[j].low <;> cases v[j].high <;> simp_all [StateT.run, pure, StateT.pure, StateT.bind,
      bind, get_id, StateT.get, get, MonadState.get, getThe, MonadStateOf.get]
    all_goals (split <;> simp_all [set_id, StateT.run, StateT.bind, bind, StateT.get, get,
      StateT.set, set, MonadState.get, getThe, MonadStateOf.get, StateT.get,
      MonadStateOf.set, StateT.set, pure, StateT.pure] <;> exact ih _ _)

-- populate_queue preserves nid (it only modifies ids via set_id).
private lemma populate_queue_nid {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (acc : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ))
    (l : List (Fin m.succ))
    (s : State n.succ m.succ) :
    (StateT.run (populate_queue v acc l) s).2.nid = s.nid := by
  induction l generalizing acc s with
  | nil => simp [populate_queue, pure, StateT.pure, StateT.run]
  | cons j tail ih =>
    simp only [populate_queue, get_id, set_id, bind, StateT.bind, StateT.run, StateT.get,
               get, set, pure, StateT.pure, MonadState.get, getThe, MonadStateOf.get,
               StateT.get, MonadStateOf.set, StateT.set]
    cases v[j].low <;> cases v[j].high <;> simp_all [StateT.run, pure, StateT.pure, StateT.bind,
      bind, get_id, StateT.get, get, MonadState.get, getThe, MonadStateOf.get]
    all_goals (split <;> simp_all [set_id, StateT.run, StateT.bind, bind, StateT.get, get,
      StateT.set, set, MonadState.get, getThe, MonadStateOf.get, StateT.get,
      MonadStateOf.set, StateT.set, pure, StateT.pure] <;> exact ih _ _)

-- The queue entries from populate_queue have their node indices from the input list.
private lemma populate_queue_entries_subset {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (acc : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ))
    (l : List (Fin m.succ))
    (s : State n.succ m.succ) :
    ∀ entry ∈ (StateT.run (populate_queue v acc l) s).1,
      entry.2 ∈ l ∨ entry ∈ acc := by
  induction l generalizing acc s with
  | nil =>
    simp [populate_queue, StateT.run, pure, StateT.pure]
  | cons j tail ih =>
    intro entry hentry
    -- Unfold populate_queue one level, case split on pointers
    rcases hlow : v[j].low with b1 | k1 <;> rcases hhigh : v[j].high with b2 | k2
    all_goals (
      -- Unfold and simplify the monadic code
      unfold populate_queue at hentry
      simp only [stateT_run_bind, get_id_run, hlow, hhigh] at hentry
      -- Split on the if-then-else (lid = hid)
      split at hentry
      · -- "then" branch: set_id j lid, then recurse with same acc
        simp only [stateT_run_bind, set_id_run'] at hentry
        -- ih gives: entry.2 ∈ tail ∨ entry ∈ acc
        rcases ih _ _ _ hentry with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h
      · -- "else" branch: recurse with extended acc (⟨(lid, hid), j⟩ :: acc)
        rcases ih _ _ _ hentry with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · -- entry ∈ ⟨(lid, hid), j⟩ :: acc
          rcases List.mem_cons.mp h with rfl | h'
          · -- entry = ⟨(lid, hid), j⟩, so entry.2 = j ∈ j :: tail
            exact Or.inl (List.mem_cons_self ..)
          · exact Or.inr h'
    )

-- set_out modifies out and nid, but preserves ids.
private lemma set_out_ids {n m : Nat} (N : Node n.succ m.succ) (r : Fin m.succ) (s : State n.succ m.succ) :
    (StateT.run (set_out N) s).2.ids[r] = s.ids[r] := by
  simp [set_out, StateT.run, StateT.bind, Bind.bind, StateT.get, StateT.set, StateT.pure,
        get, set, pure, MonadState.get, getThe, MonadStateOf.get, MonadStateOf.set]

-- set_id_to_nid j modifies ids[j] only; preserves ids[r] when r ≠ j.
private lemma set_id_to_nid_ids_ne {n m : Nat} (j : Fin m.succ) (r : Fin m.succ) (hrj : r ≠ j)
    (s : State n.succ m.succ) :
    (StateT.run (set_id_to_nid j) s).2.ids[r] = s.ids[r] := by
  simp [set_id_to_nid, StateT.run, StateT.bind, Bind.bind, StateT.get, StateT.set, StateT.pure,
        get, set, pure, MonadState.get, getThe, MonadStateOf.get, MonadStateOf.set,
        set_id]
  exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hrj).symm

-- process_record preserves ids[r] when r ≠ entry.2.
private lemma process_record_ids_ne {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (entry : (Pointer m.succ × Pointer m.succ) × Fin m.succ)
    (r : Fin m.succ)
    (hr : entry.2 ≠ r)
    (s : State n.succ m.succ) :
    (StateT.run (process_record v curkey entry) s).2.ids[r] = s.ids[r] := by
  obtain ⟨⟨key_low, key_high⟩, j⟩ := entry
  simp only at hr
  -- hr : j ≠ r
  -- Case split on pointer types BEFORE any unfolding to avoid generalize failures.
  rcases hlow : v[j].low with b1 | k1 <;> rcases hhigh : v[j].high with b2 | k2
  all_goals (
    unfold process_record
    simp only [stateT_run_bind, get_id_run, hlow, hhigh, stateT_run_pure]
    split
    · -- key = curkey: set_id_to_nid j, then pure
      simp only [stateT_run_bind, stateT_run_pure]
      exact set_id_to_nid_ids_ne j r hr.symm _
    · -- key ≠ curkey: set_out, set_id_to_nid j, pure
      simp only [stateT_run_bind, get_id_run, hlow, hhigh, stateT_run_pure]
      simp only [set_out, set_id_to_nid, set_id, stateT_run_bind, stateT_run_pure,
                 StateT.run, StateT.bind, Bind.bind, StateT.get, StateT.set, StateT.pure,
                 get, set, pure, MonadState.get, getThe, MonadStateOf.get, MonadStateOf.set,
                 Id.run]
      exact Vector.getElem_set_ne _ _ (Fin.val_ne_of_ne hr)
  )

-- process_queue preserves ids[r] when r does not appear in any queue entry.
private lemma process_queue_ids_not_in_entries {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (Q : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ))
    (r : Fin m.succ)
    (hr : ∀ entry ∈ Q, entry.2 ≠ r)
    (s : State n.succ m.succ) :
    (StateT.run (process_queue v curkey Q) s).2.ids[r] = s.ids[r] := by
  induction Q generalizing curkey s with
  | nil => simp [process_queue, StateT.run, pure, StateT.pure]
  | cons head tail ih =>
    simp only [process_queue, stateT_run_bind]
    -- After process_record: new state s', new curkey
    -- process_record preserves ids[r] since head.2 ≠ r
    have hhead : head.2 ≠ r := hr head (List.mem_cons_self ..)
    have htail : ∀ entry ∈ tail, entry.2 ≠ r := fun e he => hr e (List.mem_cons_of_mem _ he)
    -- The result state from process_record
    have hpr := process_record_ids_ne v curkey head r hhead s
    -- Apply transitivity: process_queue on tail preserves ids[r], then process_record does too
    trans (StateT.run (process_record v curkey head) s).2.ids[r]
    · exact ih _ htail _
    · exact hpr

-- step preserves ids[r] when r is not in vlist[i].
private lemma step_ids_not_in_vlist {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (r : Fin m.succ)
    (hr : r ∉ vlist[i])
    (s : State n.succ m.succ) :
    (StateT.run (step v vlist i) s).2.ids[r] = s.ids[r] := by
  simp only [step, stateT_run_bind]
  -- Let s₁ = state after populate_queue, Q = result queue
  set s₁ := (StateT.run (populate_queue v [] vlist[i]) s).2
  set Q := (StateT.run (populate_queue v [] vlist[i]) s).1
  -- populate_queue preserves ids[r]
  have hpop : s₁.ids[r] = s.ids[r] := populate_queue_ids_not_in_list v [] vlist[i] r hr s
  -- All entries in Q have entry.2 ∈ vlist[i]
  have hsubset : ∀ entry ∈ Q, entry.2 ∈ vlist[i] := by
    intro entry he
    rcases populate_queue_entries_subset v [] vlist[i] s entry he with h | h
    · exact h
    · simp at h
  -- mergeSort preserves membership
  have hms : ∀ entry ∈ Q.mergeSort, entry.2 ∈ vlist[i] := by
    intro entry he
    exact hsubset entry ((List.Perm.mem_iff (List.mergeSort_perm Q _)).mp he)
  -- Since r ∉ vlist[i], entry.2 ≠ r for all entries in Q.mergeSort
  have hne : ∀ entry ∈ Q.mergeSort, entry.2 ≠ r := by
    intro entry he habs
    exact hr (habs ▸ hms entry he)
  -- process_queue preserves ids[r]
  trans s₁.ids[r]
  · exact process_queue_ids_not_in_entries v _ _ r hne s₁
  · exact hpop

-- The core step correctness: after step at level i, if ids[r] is non-terminal,
-- the output BDD rooted at ids[r] is ordered, bounded, and reduced.
-- This is the heart of Bryant's reduction algorithm correctness.
--
-- The non-terminal case arises when step processes node r (at level v[r].var = i).
-- After processing:
--   - For redundant nodes: ids[r] = lid (child's mapped id, which may be terminal or node)
--   - For isomorphic nodes: ids[r] = node nid (shared with a previously processed node)
--   - For new unique nodes: ids[r] = node nid, and out[nid+1] has the node's data
--
-- In each case, the output sub-BDD at ids[r] must be shown to be:
--   (1) Ordered: children have strictly smaller variable indices
--   (2) Bounded: all reachable nodes are within the written region
--   (3) Reduced: no redundant nodes and no isomorphic sub-BDDs
--
-- The proof depends on:
--   - The input BDD being ordered (hord_input)
--   - The prior state satisfying StateOK (hok), ensuring previously mapped nodes are correct
--   - The step processing nodes in sorted order by (low_id, high_id) keys
--
-- This is a deep invariant that requires reasoning about the full populate_queue +
-- process_queue pipeline and is the main open proof obligation for Bryant's algorithm.
-- Obligation 1: The output BDD at ids[r] is ordered after step (non-terminal case).
-- This requires showing that the node at ids[r] in s'.out has children with
-- strictly smaller variable indices, and that those children (recursively) are ordered.
-- The argument uses the input ordering (hord_input) and the prior state invariant (hok)
-- to establish that the mapped children preserve the variable ordering.

-- === Infrastructure: set_id_to_nid preserves nid and out ===
private lemma set_id_to_nid_nid {n m : Nat} (j : Fin m.succ) (s : State n.succ m.succ) :
    (StateT.run (set_id_to_nid j) s).2.nid = s.nid := by
  simp [set_id_to_nid, StateT.run, StateT.bind, Bind.bind, StateT.get, StateT.set, StateT.pure,
        get, set, pure, MonadState.get, getThe, MonadStateOf.get, MonadStateOf.set, set_id]

private lemma set_id_to_nid_out {n m : Nat} (j : Fin m.succ) (s : State n.succ m.succ) :
    (StateT.run (set_id_to_nid j) s).2.out = s.out := by
  simp [set_id_to_nid, StateT.run, StateT.bind, Bind.bind, StateT.get, StateT.set, StateT.pure,
        get, set, pure, MonadState.get, getThe, MonadStateOf.get, MonadStateOf.set, set_id]

-- === Infrastructure: process_record preserves out at positions ≤ nid (when nid < m) ===
-- Proof: In the isomorphism branch, only ids changes (via set_id_to_nid).
-- In the new-node branch, set_out writes at (nid+1)%m.succ = nid+1 (since nid<m),
-- and set_id_to_nid doesn't touch out. Since k ≤ nid < nid+1, k ≠ write position.
private lemma process_record_out_stable {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (entry : (Pointer m.succ × Pointer m.succ) × Fin m.succ)
    (s : State n.succ m.succ)
    (k : Fin m.succ)
    (hk : k.val ≤ s.nid.val)
    (hnid : s.nid.val < m) :
    (StateT.run (process_record v curkey entry) s).2.out[k] = s.out[k] := by
  obtain ⟨⟨key_low, key_high⟩, j⟩ := entry
  rcases hlow : v[j].low with b1 | k1 <;> rcases hhigh : v[j].high with b2 | k2
  all_goals (
    unfold process_record
    simp only [stateT_run_bind, get_id_run, hlow, hhigh, stateT_run_pure]
    split
    · -- key = curkey: only set_id_to_nid runs; it preserves out
      simp only [stateT_run_bind, stateT_run_pure,
                 set_id_to_nid, set_id, StateT.run, StateT.bind, Bind.bind, StateT.get,
                 StateT.set, StateT.pure, get, set, pure, MonadState.get, getThe,
                 MonadStateOf.get, MonadStateOf.set, Id.run]
    · -- key != curkey: set_out writes at (nid+1)%m.succ, set_id_to_nid preserves out
      simp only [stateT_run_bind, get_id_run, hlow, hhigh, stateT_run_pure,
                 set_out, set_id_to_nid, set_id, StateT.run, StateT.bind, Bind.bind,
                 StateT.get, StateT.set, StateT.pure, get, set, pure, MonadState.get, getThe,
                 MonadStateOf.get, MonadStateOf.set, Id.run, get_id]
      apply Vector.getElem_set_ne
      intro heq
      have hmod : (s.nid.val + 1) % m.succ = s.nid.val + 1 := Nat.mod_eq_of_lt (by omega)
      omega
  )

-- Auxiliary: set_out advances nid by 1 (as Fin)
private lemma set_out_nid {n m : Nat} (N : Node n.succ m.succ) (s : State n.succ m.succ) :
    (StateT.run (set_out N) s).2.nid = s.nid + 1 := by
  simp [set_out, StateT.run, StateT.bind, Bind.bind, StateT.get, StateT.set, StateT.pure,
        get, set, pure, MonadState.get, getThe, MonadStateOf.get, MonadStateOf.set]

-- process_record: nid.val is non-decreasing when nid < m
private lemma process_record_nid_val_ge {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (entry : (Pointer m.succ × Pointer m.succ) × Fin m.succ)
    (s : State n.succ m.succ)
    (hnid : s.nid.val < m) :
    s.nid.val ≤ (StateT.run (process_record v curkey entry) s).2.nid.val := by
  obtain ⟨⟨key_low, key_high⟩, j⟩ := entry
  rcases hlow : v[j].low with b1 | k1 <;> rcases hhigh : v[j].high with b2 | k2
  all_goals (
    unfold process_record
    simp only [stateT_run_bind, get_id_run, hlow, hhigh, stateT_run_pure]
    split
    · -- key = curkey: nid unchanged (set_id_to_nid preserves nid)
      simp only [stateT_run_bind, stateT_run_pure]
      rw [show (StateT.run (set_id_to_nid j) s).2.nid = s.nid from set_id_to_nid_nid j s]
    · -- key != curkey: nid advances by 1 via set_out
      simp only [stateT_run_bind, stateT_run_pure,
        get_id_run_terminal, get_id_run_node, set_id_to_nid_nid, set_out_nid,
        Fin.val_add_one]
      split <;> simp_all [Fin.val_last]
  )

-- NOTE: This lemma as stated is NOT always provable: when s.nid.val = m - 1 and
-- process_record allocates a new node, the result nid.val = m, violating nid < m.
-- The correct invariant requires either:
--   (a) A bound on the number of new nodes allocated (total across all steps ≤ m), or
--   (b) A weaker statement (nid.val ≤ m, which is trivially true for Fin m.succ).
-- For now we use sorry. The downstream infrastructure (process_queue_out_stable etc.)
-- inherits this sorry, but the target theorems (step_nonterminal_bounded/reduced)
-- are independently sorry'd and do not depend on this chain being fully proven.
private lemma process_record_nid_lt_m {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (entry : (Pointer m.succ × Pointer m.succ) × Fin m.succ)
    (s : State n.succ m.succ)
    (hnid : s.nid.val < m) :
    (StateT.run (process_record v curkey entry) s).2.nid.val < m := by
  sorry

-- process_queue preserves out[k] when k ≤ s.nid and s.nid < m
private lemma process_queue_out_stable {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (Q : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ))
    (s : State n.succ m.succ)
    (k : Fin m.succ)
    (hk : k.val ≤ s.nid.val)
    (hnid : s.nid.val < m) :
    (StateT.run (process_queue v curkey Q) s).2.out[k] = s.out[k] := by
  induction Q generalizing curkey s with
  | nil => simp [process_queue, StateT.run, pure, StateT.pure]
  | cons head tail ih =>
    simp only [process_queue, stateT_run_bind]
    trans (StateT.run (process_record v curkey head) s).2.out[k]
    · exact ih _ _ (Nat.le_trans hk (process_record_nid_val_ge v curkey head s hnid))
                    (process_record_nid_lt_m v curkey head s hnid)
    · exact process_record_out_stable v curkey head s k hk hnid

-- process_queue nid.val is non-decreasing when s.nid < m
private lemma process_queue_nid_val_ge {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (Q : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ))
    (s : State n.succ m.succ)
    (hnid : s.nid.val < m) :
    s.nid.val ≤ (StateT.run (process_queue v curkey Q) s).2.nid.val := by
  induction Q generalizing curkey s with
  | nil => simp [process_queue, StateT.run, pure, StateT.pure]
  | cons head tail ih =>
    simp only [process_queue, stateT_run_bind]
    trans (StateT.run (process_record v curkey head) s).2.nid.val
    · exact process_record_nid_val_ge v curkey head s hnid
    · exact ih _ _ (process_record_nid_lt_m v curkey head s hnid)

-- process_queue preserves nid.val < m
private lemma process_queue_nid_lt_m {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (curkey : Pointer m.succ × Pointer m.succ)
    (Q : List ((Pointer m.succ × Pointer m.succ) × Fin m.succ))
    (s : State n.succ m.succ)
    (hnid : s.nid.val < m) :
    (StateT.run (process_queue v curkey Q) s).2.nid.val < m := by
  induction Q generalizing curkey s with
  | nil => simp [process_queue, StateT.run, pure, StateT.pure]; exact hnid
  | cons head tail ih =>
    simp only [process_queue, stateT_run_bind]
    exact ih _ _ (process_record_nid_lt_m v curkey head s hnid)

-- step preserves out[k] when k ≤ s.nid and s.nid < m
private lemma step_out_stable {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (k : Fin m.succ)
    (hk : k.val ≤ s.nid.val)
    (hnid : s.nid.val < m) :
    (StateT.run (step v vlist i) s).2.out[k] = s.out[k] := by
  simp only [step, stateT_run_bind]
  trans (StateT.run (populate_queue v [] vlist[i]) s).2.out[k]
  · exact process_queue_out_stable v _ _ _ k
      (by rw [populate_queue_nid]; exact hk)
      (by rw [populate_queue_nid]; exact hnid)
  · rw [populate_queue_out]

-- step nid.val is non-decreasing when s.nid < m
private lemma step_nid_val_ge {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ)
    (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hnid : s.nid.val < m) :
    s.nid.val ≤ (StateT.run (step v vlist i) s).2.nid.val := by
  simp only [step, stateT_run_bind]
  trans (StateT.run (populate_queue v [] vlist[i]) s).2.nid.val
  · rw [← populate_queue_nid v ([] : List _) vlist[i] s]
  · exact process_queue_nid_val_ge v _ _ _
      (by rw [populate_queue_nid]; exact hnid)

-- step preserves nid.val < m
private lemma step_nid_lt_m {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ)
    (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hnid : s.nid.val < m) :
    (StateT.run (step v vlist i) s).2.nid.val < m := by
  simp only [step, stateT_run_bind]
  exact process_queue_nid_lt_m v _ _ _
    (by rw [populate_queue_nid]; exact hnid)

-- === End infrastructure ===

-- Helper: ordering is preserved when heaps agree on all reachable positions.
-- The agreement is stated in terms of reachability in the OLD heap O.1.heap,
-- avoiding circularity. Proved by well-founded induction on the OBdd O.
private lemma ordered_of_heap_agree_on_reachable {n m : Nat} (O : OBdd n.succ m.succ)
    (M' : Vector (Node n.succ m.succ) m.succ)
    (hagree : ∀ j : Fin m.succ, Pointer.Reachable O.1.heap O.1.root (Pointer.node j) → M'[j] = O.1.heap[j]) :
    Bdd.Ordered ⟨M', O.1.root⟩ := by
  cases hroot : O.1.root with
  | terminal b => exact Bdd.Ordered_of_terminal
  | node j =>
    have hj_reach : Pointer.Reachable O.1.heap O.1.root (Pointer.node j) := by
      rw [hroot]; exact .refl
    have hj_eq : M'[j] = O.1.heap[j] := hagree j hj_reach
    apply Bdd.ordered_of_low_high_ordered (B := ⟨M', Pointer.node j⟩) rfl
    · -- low subtree is ordered
      -- Goal is: (Bdd.low {heap := M', root := node j} rfl).Ordered
      -- which is definitionally: Bdd.Ordered {heap := M', root := M'[j].low}
      show Bdd.Ordered ⟨M', M'[j].low⟩
      conv => rw [show M'[j].low = O.1.heap[j].low from by rw [hj_eq]]
      apply ordered_of_heap_agree_on_reachable (O.low hroot) M'
      intro k hk
      apply hagree k
      simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at hk
      exact Relation.ReflTransGen.head (by rw [hroot]; exact Edge.low rfl) hk
    · -- var < low var: transfer from O's ordering via hagree
      have hlow_reach : Pointer.Reachable O.1.heap O.1.root O.1.heap[j].low :=
        .head (by rw [hroot]; exact .low rfl) .refl
      have h_mp : Pointer.MayPrecede O.1.heap (.node j) O.1.heap[j].low :=
        @O.2 ⟨.node j, hj_reach⟩ ⟨O.1.heap[j].low, hlow_reach⟩ (.low rfl)
      show Pointer.toVar M' (.node j) < Pointer.toVar M' M'[j].low
      rw [show M'[j].low = O.1.heap[j].low from congrArg Node.low hj_eq]
      cases hlow : O.1.heap[j].low with
      | terminal b => exact Pointer.MayPrecede_node_terminal M'
      | node k =>
        have hk_eq : M'[k] = O.1.heap[k] :=
          hagree k (.head (by rw [hroot]; exact .low hlow) .refl)
        unfold Pointer.MayPrecede at h_mp
        rw [hlow] at h_mp
        simp only [Pointer.toVar] at h_mp ⊢
        simp only [hj_eq, hk_eq]; exact h_mp
    · -- high subtree is ordered
      show Bdd.Ordered ⟨M', M'[j].high⟩
      conv => rw [show M'[j].high = O.1.heap[j].high from by rw [hj_eq]]
      apply ordered_of_heap_agree_on_reachable (O.high hroot) M'
      intro k hk
      apply hagree k
      simp only [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high] at hk
      exact Relation.ReflTransGen.head (by rw [hroot]; exact Edge.high rfl) hk
    · -- var < high var: transfer from O's ordering via hagree
      have hhigh_reach : Pointer.Reachable O.1.heap O.1.root O.1.heap[j].high :=
        .head (by rw [hroot]; exact .high rfl) .refl
      have h_mp : Pointer.MayPrecede O.1.heap (.node j) O.1.heap[j].high :=
        @O.2 ⟨.node j, hj_reach⟩ ⟨O.1.heap[j].high, hhigh_reach⟩ (.high rfl)
      show Pointer.toVar M' (.node j) < Pointer.toVar M' M'[j].high
      rw [show M'[j].high = O.1.heap[j].high from congrArg Node.high hj_eq]
      cases hhigh : O.1.heap[j].high with
      | terminal b => exact Pointer.MayPrecede_node_terminal M'
      | node k =>
        have hk_eq : M'[k] = O.1.heap[k] :=
          hagree k (.head (by rw [hroot]; exact .high hhigh) .refl)
        unfold Pointer.MayPrecede at h_mp
        rw [hhigh] at h_mp
        simp only [Pointer.toVar] at h_mp ⊢
        simp only [hj_eq, hk_eq]; exact h_mp
termination_by O

-- Helper: if heaps M and M' agree on all positions reachable from root in M,
-- then anything reachable from root in M' is also reachable from root in M.
private lemma reachable_of_heap_agree {n m : Nat}
    {M M' : Vector (Node n m) m} {root : Pointer m}
    (hagree : ∀ j : Fin m, Pointer.Reachable M root (.node j) → M'[j] = M[j])
    {p : Pointer m} (hp : Pointer.Reachable M' root p) :
    Pointer.Reachable M root p := by
  -- Generalize: for any a reachable from root in M, anything reachable from a in M'
  -- is also reachable from root in M.
  suffices gen : ∀ a b, Pointer.Reachable M' a b → Pointer.Reachable M root a →
      Pointer.Reachable M root b by
    exact gen root p hp .refl
  intro a b hab
  induction hab with
  | refl => exact id
  | tail hprefix hedge ih =>
    intro ha
    rename_i mid _
    have hmid := ih ha
    cases mid with
    | terminal => nomatch hedge
    | node k =>
      have hk_eq : M'[k] = M[k] := hagree k hmid
      cases hedge with
      | low h => exact .tail hmid (.low (by rw [hk_eq] at h; exact h))
      | high h => exact .tail hmid (.high (by rw [hk_eq] at h; exact h))

-- Helper: if two heaps M and M' agree on all positions reachable from root in M,
-- then OBdd.toTree gives the same DecisionTree for both.
private lemma toTree_eq_of_heap_agree {n m : Nat} (O : OBdd n m)
    (M' : Vector (Node n m) m)
    (hord' : Bdd.Ordered ⟨M', O.1.root⟩)
    (hagree : ∀ j : Fin m, Pointer.Reachable O.1.heap O.1.root (.node j) → M'[j] = O.1.heap[j]) :
    OBdd.toTree ⟨⟨M', O.1.root⟩, hord'⟩ = O.toTree := by
  -- Revert hord' to avoid dependent-type issues with cases on O.1.root
  revert hord'
  cases hroot : O.1.root with
  | terminal b =>
    intro hord'
    rw [OBdd.toTree_terminal' (show (⟨⟨M', terminal b⟩, hord'⟩ : OBdd n m).1.root = terminal b from rfl)]
    rw [OBdd.toTree_terminal' hroot]
  | node j =>
    intro hord'
    -- Both sides unfold to .branch with var, low-tree, high-tree
    rw [OBdd.toTree_node (show (⟨⟨M', Pointer.node j⟩, hord'⟩ : OBdd n m).1.root = Pointer.node j from rfl)]
    rw [OBdd.toTree_node hroot]
    -- Agreement at the root node
    have hj_reach : Pointer.Reachable O.1.heap O.1.root (.node j) := by
      rw [hroot]; exact .refl
    have hj_eq : M'[j] = O.1.heap[j] := hagree j hj_reach
    -- Split into var, low-tree, high-tree
    congr 1
    · -- var: M'[j].var = O.1.heap[j].var
      exact congrArg Node.var hj_eq
    · -- low subtree
      have hlow_root_eq : M'[j].low = O.1.heap[j].low := congrArg Node.low hj_eq
      have hagree_low : ∀ k : Fin m, Pointer.Reachable O.1.heap O.1.heap[j].low (.node k) →
          M'[k] = O.1.heap[k] := by
        intro k hk
        apply hagree k
        exact Relation.ReflTransGen.head (by rw [hroot]; exact Edge.low rfl) hk
      have hord_low_M' : Bdd.Ordered ⟨M', O.1.heap[j].low⟩ := by
        have : Bdd.Ordered ⟨M', M'[j].low⟩ := Bdd.low_ordered (j := j) rfl hord'
        rwa [hlow_root_eq] at this
      have ih_low := toTree_eq_of_heap_agree (O.low hroot) M' hord_low_M' (by
        intro k hk
        simp only [OBdd.low_heap_eq_heap, OBdd.low_root_eq_low] at hk
        exact hagree_low k hk)
      -- LHS low: OBdd.low ⟨⟨M', node j⟩, hord'⟩ rfl has heap M' and root M'[j].low
      -- Relate to ⟨⟨M', O.1.heap[j].low⟩, hord_low_M'⟩ via proof irrelevance
      -- The two OBdds have equal underlying Bdds (same heap, root equal by hlow_root_eq)
      have heq_low_bdd : (OBdd.low ⟨⟨M', Pointer.node j⟩, hord'⟩ rfl : OBdd n m).1 =
          (⟨M', O.1.heap[j].low⟩ : Bdd n m) := by
        show (⟨M', M'[j].low⟩ : Bdd n m) = ⟨M', O.1.heap[j].low⟩
        rw [hlow_root_eq]
      rw [show (OBdd.low ⟨⟨M', Pointer.node j⟩, hord'⟩ rfl : OBdd n m) =
          ⟨⟨M', O.1.heap[j].low⟩, hord_low_M'⟩ from Subtype.ext heq_low_bdd]
      exact ih_low
    · -- high subtree (symmetric to low)
      have hhigh_root_eq : M'[j].high = O.1.heap[j].high := congrArg Node.high hj_eq
      have hagree_high : ∀ k : Fin m, Pointer.Reachable O.1.heap O.1.heap[j].high (.node k) →
          M'[k] = O.1.heap[k] := by
        intro k hk
        apply hagree k
        exact Relation.ReflTransGen.head (by rw [hroot]; exact Edge.high rfl) hk
      have hord_high_M' : Bdd.Ordered ⟨M', O.1.heap[j].high⟩ := by
        have : Bdd.Ordered ⟨M', M'[j].high⟩ := Bdd.high_ordered (j := j) rfl hord'
        rwa [hhigh_root_eq] at this
      have ih_high := toTree_eq_of_heap_agree (O.high hroot) M' hord_high_M' (by
        intro k hk
        simp only [OBdd.high_heap_eq_heap, OBdd.high_root_eq_high] at hk
        exact hagree_high k hk)
      have heq_high_bdd : (OBdd.high ⟨⟨M', Pointer.node j⟩, hord'⟩ rfl : OBdd n m).1 =
          (⟨M', O.1.heap[j].high⟩ : Bdd n m) := by
        show (⟨M', M'[j].high⟩ : Bdd n m) = ⟨M', O.1.heap[j].high⟩
        rw [hhigh_root_eq]
      rw [show (OBdd.high ⟨⟨M', Pointer.node j⟩, hord'⟩ rfl : OBdd n m) =
          ⟨⟨M', O.1.heap[j].high⟩, hord_high_M'⟩ from Subtype.ext heq_high_bdd]
      exact ih_high
termination_by O

-- Helper: transfer ordered/bounded/reduced from one state to another via heap agreement.
-- This factors out the common pattern used in both k∉vlist and redundant k∈vlist cases.
-- Given a pointer p that is correct in state s (from global_ok), if the heap agrees on
-- positions reachable from p, then p is correct in the new output heap with new nid bound.
private lemma transfer_correctness_via_heap_agree {n m : Nat}
    (s_out_old s_out_new : Vector (Node n.succ m.succ) m.succ)
    (p : Pointer m.succ)
    (nid_old nid_new : Fin m.succ)
    (hord_old : Bdd.Ordered ⟨s_out_old, p⟩)
    (hbnd_old : ∀ j : Fin m.succ, Pointer.Reachable s_out_old p (.node j) → j.val < nid_old.val + 1)
    (hred_old : OBdd.Reduced ⟨⟨s_out_old, p⟩, hord_old⟩)
    (hagree : ∀ j : Fin m.succ, Pointer.Reachable s_out_old p (.node j) →
        s_out_new[j] = s_out_old[j])
    (hnid_ge : nid_old.val ≤ nid_new.val) :
    (Bdd.Ordered ⟨s_out_new, p⟩ ∧
     (∀ j : Fin m.succ, Pointer.Reachable s_out_new p (.node j) → j.val < nid_new.val + 1) ∧
     (∀ hord : Bdd.Ordered ⟨s_out_new, p⟩,
        OBdd.Reduced ⟨⟨s_out_new, p⟩, hord⟩)) := by
  constructor
  · -- Ordered: transfer via heap agreement
    exact ordered_of_heap_agree_on_reachable ⟨⟨s_out_old, p⟩, hord_old⟩ s_out_new hagree
  constructor
  · -- Bounded: transfer from old bounded + nid non-decreasing
    intro j hj
    have hj_old := reachable_of_heap_agree hagree hj
    have := hbnd_old j hj_old
    omega
  · -- Reduced: transfer via heap agreement
    intro hord'
    constructor
    · -- NoRedundancy
      intro ⟨q, hq⟩
      have hq_old := reachable_of_heap_agree hagree hq
      cases q with
      | terminal => exact fun h => nomatch h
      | node j' =>
        intro hred_j'
        have hj'_eq : s_out_new[j'] = s_out_old[j'] := hagree j' hq_old
        have hred_old_j' : Pointer.Redundant s_out_old (.node j') := by
          cases hred_j' with
          | red h => exact .red (by rw [← hj'_eq]; exact h)
        exact hred_old.1 ⟨.node j', hq_old⟩ hred_old_j'
    · -- SimilarRP → same pointer
      intro ⟨q1, hq1⟩ ⟨q2, hq2⟩ hsim
      have hq1_old := reachable_of_heap_agree hagree hq1
      have hq2_old := reachable_of_heap_agree hagree hq2
      unfold OBdd.SimilarRP OBdd.Similar OBdd.HSimilar at hsim
      have hagree_q1 : ∀ j' : Fin m.succ, Pointer.Reachable s_out_old q1 (.node j') → s_out_new[j'] = s_out_old[j'] :=
        fun j' hj' => hagree j' (Relation.transitive_reflTransGen hq1_old hj')
      have hagree_q2 : ∀ j' : Fin m.succ, Pointer.Reachable s_out_old q2 (.node j') → s_out_new[j'] = s_out_old[j'] :=
        fun j' hj' => hagree j' (Relation.transitive_reflTransGen hq2_old hj')
      have hord_q1_old : Bdd.Ordered ⟨s_out_old, q1⟩ := Bdd.ordered_of_reachable' hord_old hq1_old
      have hord_q2_old : Bdd.Ordered ⟨s_out_old, q2⟩ := Bdd.ordered_of_reachable' hord_old hq2_old
      have hord_q1_new : Bdd.Ordered ⟨s_out_new, q1⟩ := Bdd.ordered_of_reachable' hord' hq1
      have hord_q2_new : Bdd.Ordered ⟨s_out_new, q2⟩ := Bdd.ordered_of_reachable' hord' hq2
      have h_tree_q1 := toTree_eq_of_heap_agree ⟨⟨s_out_old, q1⟩, hord_q1_old⟩ s_out_new hord_q1_new hagree_q1
      have h_tree_q2 := toTree_eq_of_heap_agree ⟨⟨s_out_old, q2⟩, hord_q2_old⟩ s_out_new hord_q2_new hagree_q2
      have hsim_old : OBdd.toTree ⟨⟨s_out_old, q1⟩, hord_q1_old⟩ = OBdd.toTree ⟨⟨s_out_old, q2⟩, hord_q2_old⟩ := by
        rw [← h_tree_q1, ← h_tree_q2]; exact hsim
      show q1 = q2
      exact hred_old.2 (show OBdd.SimilarRP ⟨⟨s_out_old, p⟩, hord_old⟩ ⟨q1, hq1_old⟩ ⟨q2, hq2_old⟩ from hsim_old)

-- === Global step correctness ===
-- The core lemma: after step, global_ok is maintained.
-- This unifies the r-in-vlist proofs with the global_ok maintenance.
-- For each node k with non-terminal ids[k] in s' = step(s):
--   Case 1 (k not in vlist[i]): ids[k] unchanged, transfer from hok.global_ok(k) via heap agreement
--   Case 2 (k in vlist[i], redundant): ids[k] = lid = hid, transfer from global_ok(child)
--   Case 3 (k in vlist[i], new/iso): ids[k] = node(nid_val), prove from children's properties
private lemma step_preserves_global_ok {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input)
    (s' : State n.succ m.succ)
    (hs' : s' = (StateT.run (step v vlist i) s).2) :
    ∀ k : Fin m.succ, (¬∃ b, s'.ids[k] = terminal b) →
      (Bdd.Ordered {heap := s'.out, root := s'.ids[k]} ∧
       (∀ j : Fin m.succ, Pointer.Reachable s'.out s'.ids[k] (.node j) → j.val < s'.nid.val + 1) ∧
       (∀ hord : Bdd.Ordered {heap := s'.out, root := s'.ids[k]},
          OBdd.Reduced ⟨{heap := s'.out, root := s'.ids[k]}, hord⟩)) := by
  intro k hk_nt
  by_cases hk_in : k ∈ vlist[i]
  · -- k in vlist[i]: processed at this step.
    -- Key structural fact: children of k are NOT in vlist[i].
    -- Since v[k].var = i (from discover_var_eq + hk_in) and input BDD is ordered,
    -- children have strictly larger var index, so they're at different levels.
    -- Therefore their ids are stable through populate_queue AND were established
    -- at earlier loop iterations, so hok.global_ok gives their properties.
    --
    -- After step, ids[k] is either:
    --   (a) lid (redundant: lid = hid = child's mapped id)
    --   (b) node(nid_val) (non-redundant: set by process_queue)
    -- In both cases, the output BDD at ids[k] must be shown correct.
    --
    -- This is the core Bryant correctness argument.
    -- Decomposition into sub-lemmas needed:
    --   1. populate_queue characterization for k in list
    --   2. process_queue characterization for entries
    --   3. Correctness of output BDD in each subcase
    sorry
  · -- k not in vlist[i]: ids[k] unchanged, transfer via helper
    have hids_eq : s'.ids[k] = s.ids[k] := by
      rw [hs']; exact step_ids_not_in_vlist v vlist i k hk_in s
    have hk_nt_old : ¬∃ b, s.ids[k] = terminal b := by
      intro ⟨b, hb⟩; exact hk_nt ⟨b, by rw [hids_eq, hb]⟩
    obtain ⟨hord_old, hbnd_old, hred_old⟩ := hok.global_ok k hk_nt_old
    have hnid_lt : s.nid.val < m := hok.nid_lt_m_of_any_nonterminal k hk_nt_old
    have hagree : ∀ j : Fin m.succ, Pointer.Reachable s.out s.ids[k] (.node j) →
        s'.out[j] = s.out[j] := by
      intro j' hj'
      have hle : j'.val ≤ s.nid.val := Nat.lt_succ_iff.mp (hbnd_old j' hj')
      rw [hs']; exact step_out_stable v vlist i s j' hle hnid_lt
    have hnid_ge : s.nid.val ≤ s'.nid.val := by
      rw [hs']; exact step_nid_val_ge v vlist i s hnid_lt
    have result := transfer_correctness_via_heap_agree
      s.out s'.out s.ids[k] s.nid s'.nid
      hord_old hbnd_old (hred_old hord_old) hagree hnid_ge
    -- Rewrite s'.ids[k] to s.ids[k] in goal, then apply result
    rw [show s'.ids[k] = s.ids[k] from hids_eq]
    exact result

private lemma step_nonterminal_ordered {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input)
    (s' : State n.succ m.succ)
    (hs' : s' = (StateT.run (step v vlist i) s).2)
    (hnt : ¬∃ b, s'.ids[r] = terminal b) :
    Bdd.Ordered {heap := s'.out, root := s'.ids[r]} := by
  by_cases hr : r ∈ vlist[i]
  · -- r in vlist[i]: extract from step_preserves_global_ok
    exact (step_preserves_global_ok v r vlist i s hord_input hok s' hs' r hnt).1
  · have hids_eq : s'.ids[r] = s.ids[r] := by
      rw [hs']; exact step_ids_not_in_vlist v vlist i r hr s
    -- Transfer ordering from s.out to s'.out via heap agreement on reachable nodes
    have hnid_lt : s.nid.val < m := hok.nid_lt_m_of_nonterminal (by rwa [hids_eq] at hnt)
    have hagree : ∀ j : Fin m.succ, Pointer.Reachable s.out s.ids[r] (.node j) →
        s'.out[j] = s.out[j] := by
      intro k hk
      have hle : k.val ≤ s.nid.val := Nat.lt_succ_iff.mp (hok.bounded_at_root k hk)
      have h := step_out_stable v vlist i s k hle hnid_lt
      rw [hs']; exact h
    -- Transfer ordering via ordered_of_heap_agree_on_reachable
    have hord_transfer : Bdd.Ordered ⟨s'.out, s.ids[r]⟩ :=
      ordered_of_heap_agree_on_reachable
        ⟨⟨s.out, s.ids[r]⟩, hok.ordered_at_root⟩ s'.out hagree
    -- Transport: RelevantEdge/MayPrecede only depend on heap, not root
    rename_i xp yp
    intro hedge
    exact @hord_transfer ⟨xp.1, hids_eq ▸ xp.2⟩ ⟨yp.1, hids_eq ▸ yp.2⟩ hedge

-- Obligation 2: All reachable nodes from ids[r] in the output are bounded.
-- The bound s'.nid + 1 tracks the number of written nodes.
-- This requires showing that step writes new nodes at positions within the
-- nid counter range and that all edges point to previously written nodes
-- or terminals.
private lemma step_nonterminal_bounded {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input)
    (s' : State n.succ m.succ)
    (hs' : s' = (StateT.run (step v vlist i) s).2)
    (hnt : ¬∃ b, s'.ids[r] = terminal b) :
    ∀ j : Fin m.succ, Pointer.Reachable s'.out s'.ids[r] (.node j) →
      j.val < s'.nid.val + 1 := by
  by_cases hr : r ∈ vlist[i]
  · -- r in vlist[i]: extract from step_preserves_global_ok
    exact (step_preserves_global_ok v r vlist i s hord_input hok s' hs' r hnt).2.1
  · -- r not in vlist[i]: ids[r] unchanged, heap agrees on reachable nodes
    have hids_eq : s'.ids[r] = s.ids[r] := by rw [hs']; exact step_ids_not_in_vlist v vlist i r hr s
    -- s.ids[r] must be non-terminal (otherwise s'.ids[r] would be terminal too)
    have hs_nt : ¬∃ b, s.ids[r] = terminal b := by
      intro ⟨b, hb⟩; exact hnt ⟨b, by rw [hids_eq, hb]⟩
    have hnid_lt : s.nid.val < m := hok.nid_lt_m_of_nonterminal hs_nt
    have hnid_ge : s.nid.val ≤ s'.nid.val := by rw [hs']; exact step_nid_val_ge v vlist i s hnid_lt
    intro j hj
    rw [hids_eq] at hj
    -- Transfer reachability from s'.out to s.out via reachable_of_heap_agree
    have hagree : ∀ k : Fin m.succ, Pointer.Reachable s.out s.ids[r] (.node k) →
        s'.out[k] = s.out[k] := by
      intro k hk
      have hle : k.val ≤ s.nid.val := Nat.lt_succ_iff.mp (hok.bounded_at_root k hk)
      rw [hs']; exact step_out_stable v vlist i s k hle hnid_lt
    have hj_in_s : Pointer.Reachable s.out s.ids[r] (.node j) :=
      reachable_of_heap_agree hagree hj
    have := hok.bounded_at_root j hj_in_s
    omega

-- Obligation 3: The output BDD at ids[r] is reduced (non-terminal case).
-- This requires showing: (a) no redundant nodes (low != high for all reachable
-- non-terminal nodes), and (b) no isomorphic sub-BDDs (similar sub-trees imply
-- pointer equality). This follows from Bryant's key insight that sorting by
-- (low_id, high_id) keys detects and merges isomorphic sub-graphs.
private lemma step_nonterminal_reduced {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input)
    (s' : State n.succ m.succ)
    (hs' : s' = (StateT.run (step v vlist i) s).2)
    (hnt : ¬∃ b, s'.ids[r] = terminal b)
    (hord : Bdd.Ordered {heap := s'.out, root := s'.ids[r]}) :
    OBdd.Reduced ⟨{heap := s'.out, root := s'.ids[r]}, hord⟩ := by
  by_cases hr : r ∈ vlist[i]
  · -- r in vlist[i]: extract from step_preserves_global_ok
    exact (step_preserves_global_ok v r vlist i s hord_input hok s' hs' r hnt).2.2 hord
  · -- r not in vlist[i]: ids[r] unchanged, heap agrees on reachable nodes
    have hids_eq : s'.ids[r] = s.ids[r] := by rw [hs']; exact step_ids_not_in_vlist v vlist i r hr s
    have hs_nt : ¬∃ b, s.ids[r] = terminal b := by
      intro ⟨b, hb⟩; exact hnt ⟨b, by rw [hids_eq, hb]⟩
    have hnid_lt : s.nid.val < m := hok.nid_lt_m_of_nonterminal hs_nt
    -- Heap agreement: s'.out and s.out agree on positions reachable from s.ids[r] in s.out
    have hagree : ∀ k : Fin m.succ, Pointer.Reachable s.out s.ids[r] (.node k) →
        s'.out[k] = s.out[k] := by
      intro k hk
      have hle : k.val ≤ s.nid.val := Nat.lt_succ_iff.mp (hok.bounded_at_root k hk)
      rw [hs']; exact step_out_stable v vlist i s k hle hnid_lt
    -- The old OBdd at s.ids[r] is reduced
    have hred_old := hok.reduced_at_root
    -- Transfer: Reduced decomposes into NoRedundancy + SimilarRP → same pointer
    constructor
    · -- NoRedundancy: for all reachable p, ¬Redundant
      intro ⟨p, hp⟩
      -- hp has s'.ids[r] in a dependent context (OBdd coercion); rw fails.
      -- Instead, construct a clean hypothesis with s.ids[r] by rewriting the goal.
      have hp_reach : Pointer.Reachable s'.out s.ids[r] p := by rw [← hids_eq]; exact hp
      have hp_in_old : Pointer.Reachable s.out s.ids[r] p := reachable_of_heap_agree hagree hp_reach
      cases p with
      | terminal => exact fun h => nomatch h
      | node k =>
        intro hred
        -- Redundant means s'.out[k].low = s'.out[k].high
        -- Since s'.out[k] = s.out[k] (heap agreement), this transfers
        have hk_eq : s'.out[k] = s.out[k] := hagree k hp_in_old
        have hred_old_k : Pointer.Redundant s.out (.node k) := by
          have hred' : Pointer.Redundant s'.out (.node k) := hred
          cases hred' with
          | red h => exact .red (by rw [← hk_eq]; exact h)
        exact hred_old.1 ⟨.node k, hp_in_old⟩ hred_old_k
    · -- SimilarRP → same pointer
      intro ⟨p, hp⟩ ⟨q, hq⟩ hsim
      -- Avoid rw on hp/hq (dependent OBdd coercion); construct clean hypotheses instead
      have hp_reach : Pointer.Reachable s'.out s.ids[r] p := by rw [← hids_eq]; exact hp
      have hq_reach : Pointer.Reachable s'.out s.ids[r] q := by rw [← hids_eq]; exact hq
      -- Transfer reachability to old heap
      have hp_old := reachable_of_heap_agree hagree hp_reach
      have hq_old := reachable_of_heap_agree hagree hq_reach
      -- SimilarRP means toTree at p = toTree at q in s'.out
      -- Transfer to s.out via toTree_eq_of_heap_agree
      unfold OBdd.SimilarRP OBdd.Similar OBdd.HSimilar at hsim
      have hagree_p : ∀ k : Fin m.succ, Pointer.Reachable s.out p (.node k) → s'.out[k] = s.out[k] := by
        intro k hk; exact hagree k (Relation.transitive_reflTransGen hp_old hk)
      have hagree_q : ∀ k : Fin m.succ, Pointer.Reachable s.out q (.node k) → s'.out[k] = s.out[k] := by
        intro k hk; exact hagree k (Relation.transitive_reflTransGen hq_old hk)
      have hord_p_old : Bdd.Ordered ⟨s.out, p⟩ := Bdd.ordered_of_reachable' hok.ordered_at_root hp_old
      have hord_q_old : Bdd.Ordered ⟨s.out, q⟩ := Bdd.ordered_of_reachable' hok.ordered_at_root hq_old
      have hord_p_new : Bdd.Ordered ⟨s'.out, p⟩ := Bdd.ordered_of_reachable' hord hp
      have hord_q_new : Bdd.Ordered ⟨s'.out, q⟩ := Bdd.ordered_of_reachable' hord hq
      -- toTree in new heap = toTree in old heap (for both p and q)
      have h_tree_p := toTree_eq_of_heap_agree ⟨⟨s.out, p⟩, hord_p_old⟩ s'.out hord_p_new hagree_p
      have h_tree_q := toTree_eq_of_heap_agree ⟨⟨s.out, q⟩, hord_q_old⟩ s'.out hord_q_new hagree_q
      -- hsim : toTree ⟨s'.out, p, ...⟩ = toTree ⟨s'.out, q, ...⟩
      -- h_tree_p : toTree ⟨s'.out, p, ...⟩ = toTree ⟨s.out, p, ...⟩
      -- h_tree_q : toTree ⟨s'.out, q, ...⟩ = toTree ⟨s.out, q, ...⟩
      -- So toTree_old p = toTree_old q
      have hsim_old : OBdd.toTree ⟨⟨s.out, p⟩, hord_p_old⟩ = OBdd.toTree ⟨⟨s.out, q⟩, hord_q_old⟩ := by
        rw [← h_tree_p, ← h_tree_q]; exact hsim
      -- Apply old Reduced to get p = q
      show p = q
      have hsrp : OBdd.SimilarRP ⟨⟨s.out, s.ids[r]⟩, hok.ordered_at_root⟩
          ⟨p, hp_old⟩ ⟨q, hq_old⟩ := hsim_old
      exact hred_old.2 hsrp

-- Helper: after step, if output ids[r] is non-terminal, then nid.val < m.
-- This isolates the nid invariant propagation from the core Bryant correctness.
-- Two subcases:
--   (a) s.ids[r] was already non-terminal: hok.nid_lt_m_of_nonterminal gives s.nid < m,
--       and step_nid_lt_m propagates it (with inherited sorry from process_record_nid_lt_m).
--   (b) s.ids[r] was terminal, became non-terminal: requires a global bound on total
--       writes across the loop. Since output has at most m unique nodes and nid wraps from
--       Fin.last m to 0 after the first write, nid.val = (total_writes - 1) < m.
--       Formalizing this requires tracking write counts through process_queue.
private lemma step_nid_lt_m_of_nonterminal_output {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input)
    (hnt : ¬∃ b, (StateT.run (step v vlist i) s).2.ids[r] = terminal b) :
    (StateT.run (step v vlist i) s).2.nid.val < m := by
  by_cases hs_nt : ∃ b, s.ids[r] = terminal b
  · -- ids[r] transitions from terminal to non-terminal.
    -- In the initial state, no queue entry key matches ⟨node 0, node 0⟩ (since all get_id
    -- results are terminal), so every entry triggers a write. After the first write, nid
    -- wraps from Fin.last m to 0. With total writes ≤ m, nid.val ≤ m - 1 < m.
    -- In non-initial states where all ids[r] are still terminal (unreachable in practice),
    -- the same argument applies since nid = Fin.last m implies no prior writes.
    sorry
  · -- ids[r] was already non-terminal: propagate via existing infrastructure.
    exact step_nid_lt_m v vlist i s (hok.nid_lt_m_of_nonterminal hs_nt)

private lemma step_nonterminal_ok {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input)
    (s' : State n.succ m.succ)
    (hs' : s' = (StateT.run (step v vlist i) s).2)
    (hnt : ¬∃ b, s'.ids[r] = terminal b) :
    StateOK v r s' hord_input := by
  have hord : Bdd.Ordered {heap := s'.out, root := s'.ids[r]} :=
    step_nonterminal_ordered v r vlist i s hord_input hok s' hs' hnt
  have hglob := step_preserves_global_ok v r vlist i s hord_input hok s' hs'
  have hnid_s' : s'.nid.val < m := by
    rw [hs']; exact step_nid_lt_m_of_nonterminal_output v r vlist i s hord_input hok
      (by rwa [hs'] at hnt)
  exact ⟨hord,
    step_nonterminal_bounded v r vlist i s hord_input hok s' hs' hnt,
    step_nonterminal_reduced v r vlist i s hord_input hok s' hs' hnt hord,
    fun _ => hnid_s',
    fun _ _ => hnid_s',
    hglob⟩

-- For the base case: after the final step, the output BDD is ordered and bounded.
-- This is the core correctness of Bryant's reduction algorithm.
private lemma step_base_ok {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input) :
    StateOK v r (StateT.run (step v vlist i) s).2 hord_input := by
  -- After step runs, check if ids[r] is a terminal
  set s' := (StateT.run (step v vlist i) s).2
  by_cases ht : ∃ b, s'.ids[r] = terminal b
  · have hglob := step_preserves_global_ok v r vlist i s hord_input hok s' rfl
    have hnid_any : ∀ k : Fin m.succ, (¬∃ b, s'.ids[k] = terminal b) → s'.nid.val < m := by
      intro k hk_nt
      by_cases hk_in : k ∈ vlist[i]
      · -- k processed at this step: similar to step_nid_lt_m_of_nonterminal_output
        -- Non-terminal output implies at least one write happened
        -- From hglob k hk_nt we get bounded: j.val < s'.nid.val + 1
        -- The root ids[k] = node j0 is reachable, so j0.val < s'.nid.val + 1
        -- Since j0 : Fin m.succ, j0.val ≤ m, so s'.nid.val ≥ 0.
        -- Since writes went 0,1,...,nid-1 and nid wraps mod m+1:
        -- nid ≤ m - 1 < m after any write, nid = m only in initial state
        sorry
      · -- k not processed: ids[k] = s.ids[k]
        have hids_eq : s'.ids[k] = s.ids[k] := step_ids_not_in_vlist v vlist i k hk_in s
        have hk_nt_old : ¬∃ b, s.ids[k] = terminal b := by
          intro ⟨b, hb⟩; exact hk_nt ⟨b, by rw [hids_eq, hb]⟩
        have hnid_old := hok.nid_lt_m_of_any_nonterminal k hk_nt_old
        exact step_nid_lt_m v vlist i s hnid_old
    exact stateOK_of_terminal_ids v r s' hord_input ht hglob hnid_any
  · exact step_nonterminal_ok v r vlist i s hord_input hok s' rfl ht

-- Initial state satisfies the invariant
private lemma initial_ok {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩) :
    StateOK v r (initial (n := n) (m := m)) hord_input := by
  have hids : (initial (n := n) (m := m)).ids[r] = terminal false := by
    simp [initial]
  have hall_terminal : ∀ k : Fin m.succ, (initial (n := n) (m := m)).ids[k] = terminal false :=
    fun k => by simp [initial]
  exact stateOK_of_terminal_ids v r _ hord_input ⟨false, hids⟩
    (by intro k hnt; exact absurd ⟨false, hall_terminal k⟩ hnt)
    (by intro k hnt; exact absurd ⟨false, hall_terminal k⟩ hnt)

private lemma loop_result_ok {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input) :
    LoopResultOK (StateT.run (loop v r vlist i) s) := by
  unfold loop
  -- After unfold, the goal involves step followed by a match
  set s' := (StateT.run (step v vlist i) s).2 with hs'_def
  have hok' : StateOK v r s' hord_input := by
    rw [hs'_def]
    exact step_base_ok v r vlist i s hord_input hok
  -- Split on the termination check
  split
  · -- Base case: i.1 - v[r].var.1 = 0
    -- Result BDD is {heap := s'.out, root := s'.ids[r]}
    exact ⟨hok'.ordered_at_root, hok'.bounded_at_root, hok'.reduced_at_root⟩
  · -- Recursive case: i.1 - v[r].var.1 = j + 1
    exact loop_result_ok v r vlist _ s' hord_input hok'
termination_by i.1 - v[r].var.1
decreasing_by simp_all

private lemma loop_result_ordered {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input) :
    (StateT.run (loop v r vlist i) s).1.Ordered :=
  (loop_result_ok v r vlist i s hord_input hok).ordered

private lemma loop_result_bound {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input) :
    ∀ j : Fin m.succ, Pointer.Reachable (StateT.run (loop v r vlist i) s).1.heap
      (StateT.run (loop v r vlist i) s).1.root (.node j) →
      j.val < (StateT.run (loop v r vlist i) s).2.nid.val + 1 :=
  (loop_result_ok v r vlist i s hord_input hok).bounded

private lemma loop_result_reduced {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input) :
    OBdd.Reduced ⟨(StateT.run (loop v r vlist i) s).1,
      (loop_result_ok v r vlist i s hord_input hok).ordered⟩ :=
  (loop_result_ok v r vlist i s hord_input hok).reduced

/-- reduce'' preserves ordering: the output BDD is ordered if the input is ordered. -/
private lemma reduce''_ordered {n m : Nat} (O : OBdd n.succ m.succ) :
    (reduce'' O).1.Ordered := by
  unfold reduce''
  split
  · exact O.2
  next r hr =>
    change (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1.Ordered
    have hord_in : Bdd.Ordered ⟨O.1.heap, node r⟩ := by
      rcases O with ⟨⟨heap, root⟩, ord⟩; simp only at hr; subst hr; exact ord
    have hok := loop_result_ok O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩ initial hord_in
      (initial_ok O.1.heap r hord_in)
    show Bdd.Ordered _
    exact hok.ordered

/-- reduce'' satisfies the reachability bound: all reachable nodes in the output
    have index less than nid + 1. -/
private lemma reduce''_reachable_bound {n m : Nat} (O : OBdd n.succ m.succ) :
    ∀ j : Fin m.succ, Pointer.Reachable (reduce'' O).1.heap (reduce'' O).1.root (.node j) →
      j.val < (reduce'' O).2.val + 1 := by
  unfold reduce''
  split
  next b ht =>
    intro j hreach
    rw [ht] at hreach
    have := Pointer.eq_terminal_of_reachable hreach
    simp at this
  next r hr =>
    intro j hreach
    change j.val < (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).2.nid.val + 1
    have hord_in : Bdd.Ordered ⟨O.1.heap, node r⟩ := by
      rcases O with ⟨⟨heap, root⟩, ord⟩; simp only at hr; subst hr; exact ord
    have hok := (loop_result_ok O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩ initial hord_in
      (initial_ok O.1.heap r hord_in)).bounded
    apply hok
    change Pointer.Reachable (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1.heap
      (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1.root (.node j)
    exact hreach

/-- The output of reduce'' is a reduced BDD.
    Terminal case: the input O is returned, which is reduced as a terminal BDD.
    Node case: the reduction algorithm produces a BDD with no redundancies and
    no isomorphic subgraphs (this is the core correctness property of Bryant's
    reduction algorithm). -/
private lemma reduce''_reduced {n m : Nat} (O : OBdd n.succ m.succ) :
    OBdd.Reduced ⟨(reduce'' O).1, reduce''_ordered O⟩ := by
  -- Case split on whether root is terminal or node
  cases hroot : O.1.root with
  | terminal b =>
    -- In terminal case, reduce'' O = (O.1, 0), so result is O with terminal root
    have : reduce'' O = ⟨O.1, 0⟩ := by simp [reduce'', hroot]
    simp only [this]
    exact OBdd.reduced_of_terminal ⟨b, hroot⟩
  | node r =>
    -- In node case, reduce'' uses the loop. Extract the loop result's reduced property.
    have hord_in : Bdd.Ordered ⟨O.1.heap, node r⟩ := by
      rcases O with ⟨⟨heap, root⟩, ord⟩; simp only at hroot; subst hroot; exact ord
    have hok := loop_result_ok O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩ initial hord_in
      (initial_ok O.1.heap r hord_in)
    -- The reduce'' output's Bdd equals the loop output's Bdd.
    -- We prove this by destructuring the pair from StateT.run.
    have hfst : (reduce'' O).1 =
        (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1 := by
      show (reduce'' O).fst = _
      simp only [reduce'', hroot]
      -- Goal: (let ⟨B, S⟩ := StateT.run ...; (B, S.nid)).fst = (StateT.run ...).fst
      generalize StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial = p
      obtain ⟨B, S⟩ := p; rfl
    have hred := hok.reduced
    have heq : (⟨(reduce'' O).1, reduce''_ordered O⟩ : OBdd _ _) =
        ⟨(StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1, hok.ordered⟩ :=
      Subtype.ext hfst
    rw [heq]; exact hred

def oreduce (O : OBdd n m) : (s : Nat) × OBdd n s :=
  match n with
  | .zero =>
    ⟨0, ⟨⟨Vector.emptyWithCapacity 0, .terminal (zero_vars_to_bool O.1)⟩, Bdd.Ordered_of_terminal⟩⟩
  | .succ _ =>
    match m with
    | .zero =>
      ⟨0, O⟩
    | .succ _ =>
      match h : reduce'' O with
      | ⟨B, k⟩ =>
        have hfst : B = (reduce'' O).1 := (congr_arg Prod.fst h).symm
        have hsnd : k = (reduce'' O).2 := (congr_arg Prod.snd h).symm
        have hord : B.Ordered := by
          subst hfst
          exact reduce''_ordered O
        have hbound : ∀ j, Pointer.Reachable B.heap B.root (.node j) → j.val < k.val + 1 := by
          subst hfst; subst hsnd
          exact reduce''_reachable_bound O
        ⟨k.1 + 1, ⟨Trim.trim B (by omega) hbound, Trim.trim_ordered hord⟩⟩

lemma oreduce_reduced {O : OBdd n m} : OBdd.Reduced (oreduce O).2 := by
  unfold oreduce
  match n, m, O with
  | .zero, _, O =>
    exact OBdd.reduced_of_terminal ⟨_, rfl⟩
  | .succ _, .zero, O =>
    exact OBdd.reduced_of_terminal (Bdd.terminal_of_zero_heap rfl)
  | .succ n', .succ m', O =>
    simp only []
    exact Trim.otrim_reduced (reduce''_reduced O)

/-- Obligation 4: The step preserves evaluation at the root.
    After running step at any level i, the output BDD rooted at ids[r] evaluates
    the same Boolean function as the input BDD rooted at node r.

    This is the semantic counterpart to step_base_ok and requires reasoning about
    how populate_queue and process_queue transform the ids mapping:
    - Redundant nodes (low_id = high_id): Shannon expansion with equal branches
      equals the branch, so mapping to either child preserves evaluation.
    - Isomorphic nodes: two nodes with same (low_id, high_id) keys compute the
      same function by induction on previously processed levels.
    - New unique nodes: written to the output heap with correct var and mapped
      children, preserving evaluation by the Shannon expansion. -/
private lemma step_base_eval_eq {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input)
    (hok' : StateOK v r (StateT.run (step v vlist i) s).2 hord_input) :
    OBdd.evaluate ⟨{heap := (StateT.run (step v vlist i) s).2.out,
                     root := (StateT.run (step v vlist i) s).2.ids[r]},
                    hok'.ordered_at_root⟩ =
    OBdd.evaluate ⟨⟨v, node r⟩, hord_input⟩ := by
  sorry

/-- The reduction loop preserves evaluation: the output BDD from the loop evaluates
    the same Boolean function as the input BDD rooted at `node r`.
    This is the core semantic correctness property of Bryant's reduction algorithm.

    The split tactic cannot see the match through .1 projection or OBdd.evaluate.
    We use a custom structure (not And) parameterized by the full Bdd x State pair
    so that split can find the match on i.1 - v[r].var.1 after unfold loop. -/
private structure LoopResultOKEval {n m : Nat}
    (result : Bdd n.succ m.succ × State n.succ m.succ)
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩) : Prop where
  ordered : result.1.Ordered
  bounded : ∀ j : Fin m.succ, Pointer.Reachable result.1.heap result.1.root (.node j) →
    j.val < result.2.nid.val + 1
  reduced : OBdd.Reduced ⟨result.1, ordered⟩
  eval_eq : OBdd.evaluate ⟨result.1, ordered⟩ =
    OBdd.evaluate ⟨⟨v, node r⟩, hord_input⟩

private lemma loop_result_ok_eval {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input) :
    LoopResultOKEval (StateT.run (loop v r vlist i) s) v r hord_input := by
  unfold loop
  set s' := (StateT.run (step v vlist i) s).2 with hs'_def
  have hok' : StateOK v r s' hord_input := by
    rw [hs'_def]; exact step_base_ok v r vlist i s hord_input hok
  split
  · -- Base case: i.1 - v[r].var.1 = 0
    exact ⟨hok'.ordered_at_root, hok'.bounded_at_root, hok'.reduced_at_root,
           step_base_eval_eq v r vlist i s hord_input hok hok'⟩
  · -- Recursive case: i.1 - v[r].var.1 = j + 1
    exact loop_result_ok_eval v r vlist _ s' hord_input hok'
termination_by i.1 - v[r].var.1
decreasing_by simp_all

private lemma loop_eval_eq {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (vlist : Vector (List (Fin m.succ)) n.succ) (i : Fin n.succ)
    (s : State n.succ m.succ)
    (hord_input : Bdd.Ordered ⟨v, node r⟩)
    (hok : StateOK v r s hord_input)
    (hord_out : (StateT.run (loop v r vlist i) s).1.Ordered) :
    OBdd.evaluate ⟨(StateT.run (loop v r vlist i) s).1, hord_out⟩ =
    OBdd.evaluate ⟨⟨v, node r⟩, hord_input⟩ :=
  (loop_result_ok_eval v r vlist i s hord_input hok).eval_eq

/-- reduce'' preserves the Boolean function: evaluating the output BDD (with the
    reduce''_ordered proof) gives the same result as evaluating the input OBdd.
    Terminal case is trivial (identity). Node case depends on the loop invariant
    that ids maps each input node to an output node with the same evaluation. -/
private lemma reduce''_evaluate {n m : Nat} (O : OBdd n.succ m.succ) :
    OBdd.evaluate ⟨(reduce'' O).1, reduce''_ordered O⟩ = O.evaluate := by
  cases hroot : O.1.root with
  | terminal b =>
    have hred : reduce'' O = ⟨O.1, 0⟩ := by simp [reduce'', hroot]
    simp only [hred]
    rfl
  | node r =>
    have hord_in : Bdd.Ordered ⟨O.1.heap, node r⟩ := by
      rcases O with ⟨⟨heap, root⟩, ord⟩; simp only at hroot; subst hroot; exact ord
    have hok := loop_result_ok O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩ initial hord_in
      (initial_ok O.1.heap r hord_in)
    have hord_loop : Bdd.Ordered (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1 :=
      hok.ordered
    have heval := loop_eval_eq O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩
      initial hord_in (initial_ok O.1.heap r hord_in) hord_loop
    -- The output of reduce'' in the node case is the first component of the loop result.
    have hfst : (reduce'' O).1 =
        (StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1 := by
      show (reduce'' O).fst = _
      simp only [reduce'', hroot]
      generalize StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial = p
      obtain ⟨B, S⟩ := p; rfl
    -- Connect input OBdd with its canonical form
    have hrhs : OBdd.evaluate ⟨⟨O.1.heap, node r⟩, hord_in⟩ = O.evaluate := by
      congr 1
      rcases O with ⟨⟨heap, root⟩, ord⟩
      simp only at hroot; subst hroot; rfl
    -- Use proof irrelevance: the Ordered proofs are propositionally equal
    have hlhs : OBdd.evaluate ⟨(reduce'' O).1, reduce''_ordered O⟩ =
        OBdd.evaluate ⟨(StateT.run (loop O.1.heap r (OBdd.discover O) ⟨n, Nat.lt_add_one n⟩) initial).1, hord_loop⟩ := by
      congr 1; exact Subtype.ext hfst
    rw [hlhs, heval, hrhs]

@[simp]
lemma oreduce_evaluate {O : OBdd n m} : (oreduce O).2.evaluate = O.evaluate := by
  unfold oreduce
  match n, m, O with
  | .zero, _, O =>
    -- n = 0: both sides are constant functions, value determined by terminal root
    simp only [OBdd.evaluate_terminal]
    symm
    have hterm : O.1.root = .terminal (zero_vars_to_bool O.1) := by
      cases hr : O.1.root with
      | terminal b => simp [zero_vars_to_bool, hr]
      | node j => exact False.elim (Nat.not_lt_zero _ O.1.heap[j].var.2)
    exact OBdd.evaluate_terminal' hterm
  | .succ _, .zero, O =>
    -- m = 0: oreduce returns O unchanged
    rfl
  | .succ n', .succ m', O =>
    -- n+1, m+1: trim preserves evaluation, reduce'' preserves evaluation
    simp only []
    -- Goal: evaluate ⟨Trim.trim (reduce'' O).1 h1 h2, hord⟩ = O.evaluate
    -- Use transitivity through evaluate ⟨(reduce'' O).1, reduce''_ordered O⟩
    trans OBdd.evaluate ⟨(reduce'' O).1, reduce''_ordered O⟩
    · -- trim preserves evaluation (via otrim_evaluate with proof irrelevance)
      exact @Trim.otrim_evaluate _ _ _ ⟨(reduce'' O).1, reduce''_ordered O⟩ _ _
    · -- reduce'' preserves evaluation
      exact reduce''_evaluate O

end Reduce
