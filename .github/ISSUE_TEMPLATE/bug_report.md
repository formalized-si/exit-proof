---
name: A check fails or a statement is wrong
about: A command of this repository does not end as AGENTS.md says, or a document says something the repository does not support
labels: bug
---

**The command, and where you ran it** (operating system, CPU, version of Python; for a proof check also Lean and Rust)

**The result that AGENTS.md or the document states**

**The result that you got** (the last 30 lines of output)

**Is it about an account on mainnet or testnet?** If yes, add the output of `python3 tools/exitproof.py <account> --json`.

A way to make a tool give a better answer than its rules allow is a security report. Do not open an issue for it: see SECURITY.md.
