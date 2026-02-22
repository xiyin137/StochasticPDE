Instruction for Claude Code (IMPORTANT TO READ ALL OF THIS!):
1. do not ever use "axiom" in rigorous formalization which is what we do here
2. definitions must be rigorous and sound, theorem statements must be correct. "conceptually correct" is not good enough - prioritize accurate and proper definitions. do not simplify by cutting corners.
3. avoid placeholders whenever possible (watch out for .choose, `True := trivial`, or arbitrary choices in definitions). always write proper definitions and check files for problematic definitions.
4. do not give up on proving sorrys (especially if you have already made partial progress in a proof, don't revert to sorry while facing complexity). do not be afraid of complexity. proceed systematically.
5. do not hesitate to develop infrastructure, create new sub folders or files for infrastructure and helper lemmas (but check local folders to avoid repetition!)
6. always search mathlib for available lemmas, always check local (ModularPhysics) imports, don't repeat what is already available
7. for complex proofs, develop helper lemmas as needed. when the file gets large consider refactoring helper lemmas into other files or subfolders.
8. do not use "lake build" by itself (it causes cache issues). compile specific folders instead, e.g. `lake build ModularPhysics/RigorousQFT/SPDE/`. if there are build issues, never run `lake clean` (especially not Mathlib!) - ask the user instead.
9. read and update TODO.md
10. you can use read_references.py to read pdf files in /references/ folder. if you need to download reference papers or books in pdf, let me know.
11. when you have trouble with proof, double check that the definitions and statements are sound. document promising but unfinished/unrealized proof ideas in /test/proofideas_***.lean
12. Do not stop at proving sorrys just because "significant infrastructure" is needed. If this is the case, and that the infrastructure is not availabel in mathlib, then develop infrastructure systematically right here and right now.
13. Always verify that definitions are proper and sound!
14. When having trouble proving sorrys, check if definitions are wrong and think about whether infrastructure is missing.
15. Proof difficulty could be either due to complexity (develop infrastructures now!) or due to wrong definitions (double check definitions, structures, and theorem statements!)
16. Axiom smuggling is absolutely not allowed! Do not ever smuggle assumptions in bundled structures. Computational result cannot be assumed in definition or structure.
17. Do not "simplify" definitions. A "simplified" definition is a wrong definition!
18. type level issues are important and should be fixed as soon as possible since they might be due to improper definitions or lack of bridge lemmas
19. read and continue to update Proofideas/ files.
20. Frequently document proof ideas to avoid losing track of thoughts when running out of context window.
21. Use the Gemini MCP (`gemini_chat` / `gemini_deep_research`) to assist with proof strategy — e.g. ask about mathematical facts, standard proof techniques, whether a theorem holds, or get references. This is especially useful for complex mathematical arguments where domain knowledge from the physics/math literature is needed.
22. It helps to write the proof attempt with a first draft, document what works and what needs adjustment, and iterate. Write the proof and compile to see what the goal state looks like.