<h1>A general formalised framework for reasoning about display calculi</h1>
This repo contains the Coq/Rocq files associated with the paper "A general formalised framework for reasoning about display calculi" by Rajeev Goré and Anthony Peigné.
This project formalises a framework for display calculus and cut-elimination that is applicable to many possible logics. It also formalises a proof of decidability of a display calculus for CPL within that framework.

<h2>Building instructions</h2>
The project requires Coq version 8.18.0 and may not compile on other versions. To obtain that version with <a href=https://opam.ocaml.org/doc/Install.html>opam</a>, simply run <code>opam pin coq 8.18.0</code>.
Compilation also requires the package <a href=https://github.com/rocq-community/aac-tactics/tree/v8.18>aac-tactics</a> that can be installed via opam with
<pre>
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-aac-tactics
</pre>

Then it suffices to run <code>make</code> or <code>make all</code> at the root directory to compile all the files. This will also extract OCaml cut-elimination programs for CPL, Kt, and Lambek calculus.
