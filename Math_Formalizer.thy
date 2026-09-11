theory Math_Formalizer
  imports "HOL-Algebra.Algebra"
begin

section \<open>A simplifier term order that knows the ring operations of HOL-Algebra\<close>

text \<open>
  Importing this theory changes one thing: the term order the simplifier uses to decide whether a
  permutative rewrite rule (commutativity, left-commutativity, \dots) may fire. The ring operations
  of HOL-Algebra get the precedence \<open>zero < add < a_inv < a_minus < one < mult\<close>, the same
  one the @{method algebra} method uses internally, so that
  \<open>simp add: ring_simprules\<close> (or \<open>cring_simprules\<close>) normalises ring expressions
  the way @{method algebra} does. Terms not headed by a ring operation are compared by the default
  order, so nothing changes for other operators. See \<^file>\<open>ring_term_ord.ML\<close> for the
  details and the known behavioural consequence.
\<close>

ML_file \<open>ring_term_ord.ML\<close>

setup \<open>Ring_Term_Ord.setup\<close>

end
