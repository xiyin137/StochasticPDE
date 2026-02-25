# Codex/Claude Agent Guidance for StochasticPDE

This file is the working guidance for coding agents in this repository.

## Core rigor rules

1. Never introduce `axiom` (or any assumption-smuggling equivalent) in Lean code.
2. Prioritize fully correct, sound definitions over shortcuts.
3. Avoid fake definitions and placeholder constructions (`True := trivial`, unjustified `.choose`, arbitrary junk terms) unless mathematically justified.
4. Do not use placeholder models/definitions to close goals; this applies to both test/scratch files and main files.
5. Do not "simplify" definitions if it changes meaning; simplified but wrong definitions are not acceptable.
6. If a proof fails, check in this order: statement correctness, definition correctness, then missing infrastructure.
7. Do not weaken theorem statements only to make proofs easier.
8. Type-level issues are high-priority and often indicate wrong definitions or missing bridge lemmas.
9. Computational results must be proved as theorems, not embedded as assumed structure fields.

## Sorry-closing workflow

1. Do not give up on `sorry` proofs; proceed systematically.
2. For substantial proofs, create helper lemmas and infrastructure rather than brittle one-shot proofs.
3. Reuse existing lemmas first: search Mathlib and local `StochasticPDE` imports before re-proving.
4. If a proof remains blocked, write down proof ideas in `test/proofideas_*.lean` or relevant `Proofideas/` notes.
5. Keep `TODO.md` and proof-idea notes updated as progress is made.
6. If infrastructure is missing, build it now instead of parking the main proof.

## Build and tooling rules

1. Do not run bare `lake build`; use targeted builds (`lake env lean <file>` or `lake build <module>`).
2. Never run `lake clean` unless explicitly approved by the user.
3. Use `read_references.py` for PDFs in `references/` when needed.
4. If available, use strategy-assist tools (for example Gemini MCP) for math/proof references and techniques.

## Practical proof tactics

1. Write proof drafts early and compile to inspect goal states.
2. Split long proofs into local/private helper lemmas with explicit names.
3. Promote broadly useful infrastructure into reusable files/subfolders instead of duplicating it.
4. Validate soundness continuously; successful compilation is necessary but not sufficient.
