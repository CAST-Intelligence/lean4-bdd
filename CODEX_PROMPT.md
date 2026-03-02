# Codex Prompt: Bryant BDD Reduction -- 6 Sorry Closeout

## Context

We are verifying Bryant's BDD reduction algorithm in Lean 4 (toolchain 4.28.0). The file
`Bdd/Reduce.lean` (~2670 lines) implements the reduction function and its correctness proofs.
The algorithm processes a BDD bottom-up level by level:

1. `populate_queue`: at each level, classifies nodes as redundant (low_id = high_id, mapped
   to child) or non-redundant (added to queue with (low_id, high_id) key).
2. `process_queue`: processes sorted queue. Consecutive entries with same key are isomorphic
   (share one output node). New keys get a fresh output node via `set_out`.
3. `step`: composes populate_queue + mergeSort + process_queue for one level.
4. `loop`: iterates step from top level down to root's level.

The file builds on a lean4-bdd library (Yaron Minsky thesis port). Current state: **6 sorry
holes, everything else compiles** (952 jobs, 0 errors).

## Key Data Structures

```lean
private structure State (n) (m) where
  out : Vector (Node n m) m          -- output heap
  ids : Vector (Pointer m) m         -- mapping from input node index to output pointer
  nid : Fin m                        -- next free output slot

private def initial {n m : Nat} : State n.succ m.succ :=
  { out := Vector.replicate m.succ {var := 0, low := terminal false, high := terminal true},
    ids := Vector.replicate m.succ (terminal false),
    nid := Fin.last m }
```

Note: `initial.nid = Fin.last m` (value = m). `set_out` writes at position
`(nid.val + 1) % m.succ` and increments nid by 1. So the first write goes to position
`(m+1) % (m+1) = 0`, next to 1, etc.

```lean
private structure StateOK {n m : Nat}
    (v : Vector (Node n.succ m.succ) m.succ) (r : Fin m.succ)
    (s : State n.succ m.succ) (hord_input : Bdd.Ordered <v, node r>) : Prop where
  ordered_at_root : Bdd.Ordered {heap := s.out, root := s.ids[r]}
  bounded_at_root : forall j, Reachable s.out s.ids[r] (.node j) -> j.val < s.nid.val + 1
  reduced_at_root : OBdd.Reduced <{heap := s.out, root := s.ids[r]}, ordered_at_root>
  global_ok : forall k, (not exists b, s.ids[k] = terminal b) ->
    (Bdd.Ordered {heap := s.out, root := s.ids[k]} /\
     (forall j, Reachable s.out s.ids[k] (.node j) -> j.val < s.nid.val + 1) /\
     (forall hord, OBdd.Reduced <{heap := s.out, root := s.ids[k]}, hord>))
  var_ge : forall c k, s.ids[c] = node k -> v[c].var.val <= s.out[k].var.val

private def VlistOK v vlist : Prop :=
  forall i,
    (forall j in vlist[i], v[j].var = i) /\
    (forall j in vlist[i], forall c, (v[j].low = node c \/ v[j].high = node c) -> c not-in vlist[i]) /\
    vlist[i].Nodup /\
    (forall j in vlist[i], forall c, (v[j].low = node c \/ v[j].high = node c) -> v[j].var.val < v[c].var.val)
```

## The 6 Sorry Sites

### Sorry 1 & 2: `process_queue_entry_ok` (lines 1941, 1945)

The core process_queue correctness lemma. After processing a sorted queue, each entry's
mapped output (ids[entry.2]) is ordered, bounded, and reduced. Proven by induction on the
queue. The iso branch of `hcurkey_ok_tail` is closed. Two sorrys remain:

**Sorry 1 (line 1941)**: New-key case of `hcurkey_ok_tail`. When `head.1 != curkey`,
process_record writes a new output node via set_out. Need to show that after this write,
`node pr.2.nid` points to a correct sub-BDD. The new node has:
- `var = v[head.2].var`
- `low = resolve_id s (v[head.2].low)`
- `high = resolve_id s (v[head.2].high)`

The children (low, high) are correct by `hchildren_ok`. The variable ordering follows from
`hvar_lt_child`. Need to compose these.

**Sorry 2 (line 1945)**: Entry = head case. After process_queue finishes the full tail,
prove `ids[head.2]` (in the final state) maps to a correct sub-BDD. Two sub-cases:
- If `head.1 = curkey` (iso): `ids[head.2] = node s.nid`, same as the previous entry.
- If `head.1 != curkey` (new key): `ids[head.2] = node (s.nid + 1)` (the newly written
  output node). Need to show this survives process_queue on the tail.

### Sorry 3: `step_preserves_var_ge` (line 1971)

The c-in-vlist[i] case. When c was processed at this step level, and `s'.ids[c] = node k`,
prove `v[c].var.val <= s'.out[k].var.val`. Two sub-cases:
- Redundant (c mapped to child's id): `ids[c] = s.ids[c']` where v[c].low = node c' or
  similar. Chain through `hok.var_ge`.
- Non-redundant (c got fresh output node): `out[new_nid].var = v[c].var`, so equality holds.
  Need to trace through populate_queue + process_queue to connect c to its output.

### Sorry 4 & 6: Budget bound (lines 2446, 2652)

```lean
have hbound : s.nid.val + vlist[i].length <= m := by sorry
```

This appears in `loop_result_ok` and `loop_result_ok_eval`. The issue: `initial.nid = Fin.last m`
which has value m. So at the first iteration, we'd need `m + vlist[i].length <= m`, which fails
for any non-empty level.

**Key insight**: `nid` is modular. `set_out` does `(nid.val + 1) % m.succ`, and nid wraps.
After the first `set_out`, nid becomes 0 (since `(m + 1) % (m+1) = 0`). Alternatively, we
may need a different capacity tracking approach. The real invariant is something like:

> The total number of output nodes written so far (across all levels) is at most m.

This means `nid` wraps exactly once at the start and then counts up from 0. We need either:
- A "virtual nid" that tracks total writes without modular arithmetic
- A proof that after the first write, nid.val < m, and then the bound works for subsequent levels
- Or: replace `nid.val + vlist[i].length <= m` with a different invariant on remaining capacity

This is a **structural/design issue**, not just a proof gap.

### Sorry 5: `step_base_eval_eq` (line 2620)

Semantic correctness: after step at level i, the output BDD evaluates the same Boolean
function as the input. This requires reasoning about Shannon expansion:
- Redundant nodes: `f(x) = f_low(x)` when low = high (Shannon with equal branches)
- Isomorphic nodes: same (low_id, high_id) keys implies same function (by induction on
  previously processed levels)
- New unique nodes: written with correct var and mapped children, preserving evaluation

This is the deepest sorry -- it needs a semantic argument connecting the structural
properties (ordering, boundedness, reduction) to evaluation.

## Available Helper Lemmas (proven)

```
populate_queue_ids_not_in_list   -- ids[r] unchanged when r not in input list
populate_queue_out               -- out unchanged through populate_queue
populate_queue_nid               -- nid unchanged through populate_queue
populate_queue_entry_keys        -- entry keys are terminal or s.ids[c] for c outside list
populate_queue_entry_keys_child  -- entry.1.1 = node k implies exists child c with
                                 -- v[entry.2].low = node c and s.ids[c] = node k
populate_queue_entries_subset    -- entry.2 comes from the input list
populate_queue_entries_nonredundant  -- entries have lid != hid
populate_queue_nonredundant_in_queue -- non-redundant k in list has entry in queue
process_record_iso               -- iso case: returns curkey, preserves nid and out
process_record_out_stable        -- out[k] stable when k.val <= s.nid.val
process_record_nid_val_ge        -- nid non-decreasing
process_record_nid_val_le_succ   -- nid advances by at most 1
process_queue_out_stable         -- out[k] stable across full queue processing
process_queue_nid_val_ge         -- nid non-decreasing across queue
step_ids_not_in_vlist            -- ids[c] unchanged when c not in vlist[i]
step_out_stable                  -- out[k] stable when k.val <= s.nid.val
transfer_correctness_via_heap_agree  -- transfer ordered+bounded+reduced through heap agreement
reachable_of_heap_agree          -- transfer reachability through heap agreement
toTree_eq_of_heap_agree          -- OBdd.toTree invariant under heap changes at non-reachable nodes
step_preserves_global_ok         -- global_ok maintained through step (proven, 800k heartbeats)
step_preserves_var_ge            -- var_ge maintained (c-not-in-vlist case proven, c-in-vlist sorry)
discover_vlist_ok                -- discover produces VlistOK
```

## Questions for Codex

1. **Budget bound (Sorry 4/6)**: What's the right invariant to replace
   `s.nid.val + vlist[i].length <= m`? Given that nid starts at Fin.last m (value m) and wraps
   via modular arithmetic, how should we track remaining capacity? Should we:
   - Add a "total nodes written" ghost field to State?
   - Prove nid wraps exactly once and then counts linearly?
   - Use a different bound that accounts for modular arithmetic?

2. **New-key hcurkey_ok_tail (Sorry 1)**: After set_out writes node N at position
   `(nid+1)%m.succ`, how do we compose hchildren_ok (children are correct) with
   hvar_lt_child (variable ordering) to show the new node at `node nid` is a correct sub-BDD?
   The tricky part: set_out modifies out, so we need heap agreement between the pre-write
   and post-write heaps for the children's subtrees.

3. **Entry = head case (Sorry 2)**: After process_queue processes the full tail, need to
   show head.2's mapping survives. Is this a straightforward induction showing ids[head.2]
   is unchanged by process_queue on tail (since head.2 was already processed), or does it
   need more machinery?

4. **step_preserves_var_ge c-in-vlist (Sorry 3)**: For the non-redundant case, we need to
   connect c's fresh output node to its variable. We know process_record writes
   `{var := v[c].var, low := ..., high := ...}` at the next nid. But tracing this through
   populate_queue + mergeSort + process_queue is complex. What's the cleanest approach?

5. **step_base_eval_eq (Sorry 5)**: This is the semantic correctness. Any suggestions for
   the proof structure? Should we:
   - Prove it by induction on levels processed?
   - Use a simulation argument (each step maintains eval equivalence)?
   - Factor through a "toTree equivalence" argument?

## Project Setup

This is a standalone Lean 4 project at `ai_docs/lean4-bdd/` within a larger repo.
Work exclusively in this directory.

```
ai_docs/lean4-bdd/
  lakefile.toml          # Lake project config
  lean-toolchain         # leanprover/lean4:v4.28.0
  Bdd/
    Basic.lean           # BDD types: Pointer, Node, Bdd, Edge, Reachable
    BddTree.lean         # Tree type, OBdd.toTree
    Ordered.lean         # Bdd.Ordered, OBdd, ordered_of_reachable
    Reduced.lean         # OBdd.Reduced (NoRedundancy + SimilarRP injectivity)
    Evaluate.lean        # OBdd.evaluate (Shannon expansion)
    Collect.lean         # collect: reachable node enumeration
    Trim.lean            # otrim: trim unreachable nodes
    Reduce.lean          # THE TARGET FILE (Bryant reduction + proofs, ~2670 lines)
```

### Build

```bash
cd ai_docs/lean4-bdd
lake build              # builds all (depends on mathlib v4.28.0)
```

Mathlib is a dependency (for List.mergeSort, Vector, etc). First build fetches it.

### Verify sorry count

```bash
grep -n 'sorry' Bdd/Reduce.lean
```

Should show 6 lines.

## Branch & Commit

Branch: `lean-4.28-compat`, commit: `d006568`
File: `Bdd/Reduce.lean`
Lean toolchain: `leanprover/lean4:v4.28.0`

## Task

Analyze the 6 sorry sites and propose concrete proof strategies. You may:
- Write proof sketches (tactic-mode Lean 4)
- Suggest new helper lemmas with signatures
- Propose restructuring of invariants (especially for the budget bound)
- Point out if any sorry is fundamentally unprovable as stated and needs restating

Focus on actionable strategies rather than general advice. Reference line numbers and
existing lemma names. If you write code, make sure it uses Lean 4 syntax (not Lean 3).
