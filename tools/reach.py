"""Static reachability from wasm exports to NEAR host functions that change who controls an account.

Input: a .wasm file; uses the text form printed by `wasm-tools print`.

Indirect calls. Rust compiles trait-object calls to
    <vtable ptr>; i32.load offset=K; call_indirect (type T)
where K is the method slot. We rebuild the vtables from the module's data
segments (a vtable = [drop_in_place, size, align, method...] of table indices)
and resolve such a site to the functions found at slot K of any vtable whose
signature matches T. A site whose index does not come from `i32.load offset=K`
falls back to every table function with signature T (plain over-approximation).

Modes:
  precise (default) - vtable slot resolution + address-taken constants for fallback sites
  coarse            - every call_indirect resolves to every table function of the same signature
Assumption of `precise`: indirect calls go through vtables kept in the module's
initial data or through table indices that appear as constants in the code. Both
are true for code emitted by rustc; pointer arithmetic on table indices would break it.
"""
import collections
import json
import re
import subprocess
import sys

CONTROL = {
    "promise_batch_action_deploy_contract": "deploy_code",
    "promise_batch_action_add_key_with_full_access": "add_full_access_key",
    "promise_batch_action_add_gas_key_with_full_access": "add_full_access_key",
    "promise_batch_action_delete_account": "delete_account",
    "promise_batch_action_use_global_contract": "use_global_by_hash",
    "promise_batch_action_use_global_contract_by_account_id": "use_global_by_account",
    "promise_batch_action_deploy_global_contract": "deploy_global",
    "promise_batch_action_deploy_global_contract_by_account_id": "deploy_global_by_account",
    "promise_batch_action_transfer": "transfer_near",
    "promise_batch_action_stake": "stake",
    "promise_batch_action_add_key_with_function_call": "add_fc_key",
    "promise_batch_action_delete_key": "delete_key",
}
CODE_CHANGE = {"deploy_code", "add_full_access_key", "delete_account", "use_global_by_account", "use_global_by_hash"}

ESC = re.compile(rb"\\([0-9a-fA-F]{2}|n|t|r|\\|\"|')")


def unescape(s):
    raw = s.encode("latin-1")
    out = bytearray()
    i = 0
    while i < len(raw):
        c = raw[i]
        if c == 0x5C:
            nxt = raw[i + 1:i + 3]
            if re.match(rb"[0-9a-fA-F]{2}", nxt):
                out.append(int(nxt, 16))
                i += 3
                continue
            m = {ord("n"): 10, ord("t"): 9, ord("r"): 13, ord("\\"): 92, ord('"'): 34, ord("'"): 39}[raw[i + 1]]
            out.append(m)
            i += 2
            continue
        out.append(c)
        i += 1
    return bytes(out)


def wat(path):
    return subprocess.run(["wasm-tools", "print", path], capture_output=True, text=True, check=True).stdout


def parse(text):
    types, imports, funcs, ftype, exports = {}, {}, {}, {}, {}
    table = {}  # table index -> func
    data = []  # (addr, bytes)
    consts = set()
    cur = None
    prev = None
    for ln in text.split("\n"):
        if ln.startswith("  (type (;"):
            m = re.match(r"  \(type \(;(\d+);\) \(func(.*)\)\)\s*$", ln)
            if m:
                types[int(m.group(1))] = m.group(2).strip()
            cur = None
        elif ln.startswith("  (import "):
            m = re.match(r"  \(import \"([^\"]+)\" \"([^\"]+)\" \(func \(;(\d+);\) \(type (\d+)\)", ln)
            if m:
                i = int(m.group(3))
                imports[i] = m.group(2) if m.group(1) == "env" else m.group(1) + "." + m.group(2)
                ftype[i] = int(m.group(4))
            cur = None
        elif ln.startswith("  (func "):
            m = re.match(r"  \(func (?:\$\S+ )?\(;(\d+);\) \(type (\d+)\)", ln)
            cur = int(m.group(1))
            ftype[cur] = int(m.group(2))
            funcs[cur] = {"calls": set(), "ind": []}
            prev = None
        elif ln.startswith("  (export "):
            m = re.match(r"  \(export \"([^\"]+)\" \(func (\d+)\)\)", ln)
            if m:
                exports[m.group(1)] = int(m.group(2))
            cur = None
        elif ln.startswith("  (elem"):
            m = re.match(r"  \(elem (?:\(;\d+;\) )?\(i32\.const (\d+)\) func ([\d ]+)\)", ln)
            if m:
                base = int(m.group(1))
                for k, f in enumerate(m.group(2).split()):
                    table[base + k] = int(f)
            cur = None
        elif ln.startswith("  (data"):
            m = re.match(r"  \(data (?:\(;\d+;\) )?\(i32\.const (\d+)\) \"(.*)\"\)\s*$", ln)
            if m:
                data.append((int(m.group(1)), unescape(m.group(2))))
            cur = None
        elif ln.startswith("  (") or ln.startswith(")"):
            cur = None
        elif cur is not None:
            s = ln.strip()
            m = re.match(r"(?:return_)?call (\d+)\b", s)
            if m:
                funcs[cur]["calls"].add(int(m.group(1)))
                prev = s
                continue
            m = re.match(r"(?:return_)?call_indirect(?: \d+)? \(type (\d+)\)", s)
            if m:
                k = None
                if prev is not None:
                    pm = re.match(r"i32\.load(?: offset=(\d+))?(?: align=\d+)?$", prev)
                    if pm:
                        k = int(pm.group(1) or 0)
                funcs[cur]["ind"].append((int(m.group(1)), k))
            m = re.match(r"i32\.const (-?\d+)$", s)
            if m:
                consts.add(int(m.group(1)))
            prev = s
    return types, imports, funcs, ftype, exports, table, data, consts


def build_memory(data):
    mem = {}
    for addr, b in data:
        for i, x in enumerate(b):
            mem[addr + i] = x
    return mem


def word(mem, a):
    try:
        return mem[a] | mem[a + 1] << 8 | mem[a + 2] << 16 | mem[a + 3] << 24
    except KeyError:
        return None


def analyse(path, mode="precise"):
    types, imports, funcs, ftype, exports, table, data, consts = parse(wat(path))
    sig = {i: types.get(t, "?") for i, t in ftype.items()}
    drop_sig = "(param i32)"
    mem = build_memory(data)
    # vtable starts: [drop fn (table idx of a (param i32) fn), size, align in {1,2,4,8,16}]
    vt = []
    for addr, b in data:
        for a in range(addr - addr % 4, addr + len(b) - 11, 4):
            d, sz, al = word(mem, a), word(mem, a + 4), word(mem, a + 8)
            if d is None or sz is None or al is None:
                continue
            if d in table and sig.get(table[d]) == drop_sig and al in (1, 2, 4, 8, 16) and sz < (1 << 24):
                vt.append(a)
    bysig = collections.defaultdict(set)
    for t, f in table.items():
        bysig[sig.get(f)].add(f)
    taken = collections.defaultdict(set)
    for c in consts:
        if c in table:
            taken[sig.get(table[c])].add(table[c])
    slot_cache = {}

    def slot_targets(k, s):
        key = (k, s)
        if key not in slot_cache:
            out = set()
            for a in vt:
                w = word(mem, a + k)
                if w is not None and w in table and sig.get(table[w]) == s:
                    out.add(table[w])
            slot_cache[key] = out
        return slot_cache[key]

    def succ(f):
        if f not in funcs:
            return set()
        out = set(funcs[f]["calls"])
        for ty, k in funcs[f]["ind"]:
            s = types.get(ty)
            if mode == "coarse":
                out |= bysig.get(s, set())
            elif k is not None:
                out |= slot_targets(k, s)
            else:
                out |= taken.get(s, set())
        return out

    succ_cache = {f: succ(f) for f in funcs}

    def reach(start):
        seen, st = {start}, [start]
        while st:
            f = st.pop()
            for g in succ_cache.get(f, ()):
                if g not in seen:
                    seen.add(g)
                    st.append(g)
        return seen

    res = {}
    for name, f in sorted(exports.items()):
        r = reach(f)
        res[name] = sorted({CONTROL[imports[g]] for g in r if imports.get(g) in CONTROL})
    imported = sorted({CONTROL[n] for n in imports.values() if n in CONTROL})
    ind_sites = sum(len(v["ind"]) for v in funcs.values())
    slot_sites = sum(1 for v in funcs.values() for _, k in v["ind"] if k is not None)
    return {
        "mode": mode,
        "exports": res,
        "imported_control": imported,
        "code_change_exports": {k: [x for x in v if x in CODE_CHANGE] for k, v in res.items() if set(v) & CODE_CHANGE},
        "n_funcs": len(funcs),
        "n_table": len(table),
        "n_vtables": len(vt),
        "n_indirect_sites": ind_sites,
        "n_slot_resolved_sites": slot_sites,
    }


if __name__ == "__main__":
    mode = "coarse" if "--coarse" in sys.argv else "precise"
    r = analyse(sys.argv[1], mode)
    if "--json" in sys.argv:
        print(json.dumps(r, indent=1))
        sys.exit()
    print(f"mode={mode} funcs={r['n_funcs']} table={r['n_table']} vtables={r['n_vtables']} indirect={r['n_indirect_sites']} slot-resolved={r['n_slot_resolved_sites']}")
    print("imported control:", r["imported_control"])
    for k, v in r["exports"].items():
        if v:
            print(f"  {k:34s} -> {v}")
