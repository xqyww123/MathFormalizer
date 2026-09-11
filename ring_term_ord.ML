(*  Title:      MathFormalizer/ring_term_ord.ML

A term order for ordered rewriting in the simplifier that knows the ring operations of
HOL-Algebra.

The simplifier applies a permutative rewrite rule (commutativity, left-commutativity, ...) only
if the result is smaller in the simpset's term order. The default order, Term_Ord.term_ord,
compares by term size first, which does not yield a useful normal form for ring expressions:
e.g. it keeps "a" and "\<ominus> a" apart in "a \<oplus> (b \<oplus> \<ominus> a)", so the
cancellation rules never match. The order below is a lexicographic path ordering in which the
ring operations get a precedence (zero < add < a_inv < a_minus < one < mult), the same precedence
the "algebra" method of HOL-Algebra.Ring uses. Anything not headed by a ring operation is compared
by the default order, so AC normal forms of other operators are unchanged.

A ring operation applied to its structure argument ("add R", "zero F") is treated as one symbol:
only the operands take part in the subterm rule, and the same operation on different structures
is ordered by the structure terms. Letting the structure argument take part in the subterm rule
would make the result depend on the name of the variable being compared (a fixed "a" and the
simplifier's own bound variable ":000" compare differently against a structure "F"), and the same
term would get different normal forms in a conclusion and in a premise.

Behavioural consequence: the constants "zero R" and "one R" are ordered before variables, whereas
the default order puts them after (they are bigger terms). Proofs that rely on commutativity
turning "\<zero> \<oplus> x" into "x \<oplus> \<zero>" (or the other way round) are sensitive to
this. Give both orientations of such rules, or use "algebra", where that matters.
*)

signature RING_TERM_ORD =
sig
  val ring_ops: string list
  val dest_ring: term -> (int * term * term list) option
  val term_ord: term ord
  val setup: theory -> theory
end;

structure Ring_Term_Ord: RING_TERM_ORD =
struct

val ring_ops =
  [@{const_name Ring.ring.zero}, @{const_name Ring.ring.add}, @{const_name Ring.a_inv},
   @{const_name Ring.a_minus}, @{const_name Group.monoid.one}, @{const_name Group.monoid.mult}];

fun rank (Const (c, _)) = find_index (fn d => c = d) ring_ops
  | rank _ = ~1;

(*a ring operation applied to its structure argument: (precedence, structure, operands)*)
fun dest_ring t =
  (case strip_comb t of
    (f, str :: ops) => let val r = rank f in if r >= 0 then SOME (r, str, ops) else NONE end
  | _ => NONE);

fun term_ord (s, t) =
  (case (dest_ring s, dest_ring t) of
    (NONE, NONE) => Term_Ord.term_ord (s, t)
  | (ds, dt) =>
      let
        val ss = (case ds of SOME (_, _, ops) => ops | NONE => snd (strip_comb s));
        val ts = (case dt of SOME (_, _, ops) => ops | NONE => snd (strip_comb t));
        val hd_ord =
          (case (ds, dt) of
            (SOME (r1, str1, _), SOME (r2, str2, _)) =>
              (case int_ord (r1, r2) of EQUAL => Term_Ord.term_ord (str1, str2) | ord => ord)
          | (SOME _, NONE) => LESS
          | (NONE, SOME _) => GREATER
          | (NONE, NONE) => EQUAL);
      in
        if forall (fn si => term_ord (si, t) = LESS) ss then
          (case hd_ord of
            GREATER => if forall (fn ti => term_ord (s, ti) = GREATER) ts then GREATER else LESS
          | EQUAL =>
              if forall (fn ti => term_ord (s, ti) = GREATER) ts
              then list_ord term_ord (ss, ts) else LESS
          | LESS => LESS)
        else GREATER
      end);

val setup = Context.theory_map (Raw_Simplifier.map_ss (Raw_Simplifier.set_term_ord term_ord));

end;
