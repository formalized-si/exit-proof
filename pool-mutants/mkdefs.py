# Build StakingPool/WorldDefs.lean from World.lean: keep defs/structures/inductives/instances, drop theorems and WInv.
import re, sys
src = open(sys.argv[1]).read()
src = src.replace("import StakingPool.Methods", "import StakingPool.Model")
lines = src.split("\n")
out, i = [], 0
# split into top-level blocks: a block starts at a line beginning with a keyword or a doc comment
starts = re.compile(r"^(/--|theorem |@\[simp\] theorem |def |structure |inductive |instance |namespace |end |import |/-)")
blocks, cur = [], []
for l in lines:
    if starts.match(l) and cur:
        blocks.append(cur); cur = []
    cur.append(l)
blocks.append(cur)
# attach doc comments to the following block
merged, pend = [], []
for b in blocks:
    if b[0].startswith("/--"):
        pend += b; continue
    merged.append(pend + b); pend = []
keep = []
for b in merged:
    kw = re.compile(r"^(theorem |@\[simp\] theorem |def |structure |inductive |instance |namespace |end |import )")
    head = next((l for l in b if kw.match(l)), b[0])
    if re.match(r"^(theorem|@\[simp\] theorem)", head): continue
    if head.startswith("structure WInv"): continue
    if head.startswith("inductive Reach"): continue
    keep.append("\n".join(b))
open(sys.argv[2], "w").write("\n".join(keep) + "\n")
