theory Math_Formalizer_Tests
  imports Math_Formalizer
begin

section \<open>Controls: AC normal forms of operators other than the ring operations are unchanged\<close>

ML_val \<open>
  val ctxt = @{context};
  val ctxt0 = Raw_Simplifier.set_term_ord Term_Ord.term_ord ctxt;
  fun nf c t =
    Thm.term_of (Thm.rhs_of (Simplifier.rewrite (c addsimps @{thms ac_simps}) (Thm.cterm_of c t)));
  val ts =
    [@{term "(x::nat) + (z + y) * w"}, @{term "(a::int) * (c * b) + b"},
     @{term "f (z::nat) + g y + x"}, @{term "A \<union> (C \<union> B) \<inter> D"},
     @{term "(z::nat) + y + x + (w + v) * (u * t)"}];
  val _ = ts |> List.app (fn t =>
    let val (a, b) = (nf ctxt t, nf ctxt0 t) in
      if a aconv b then ()
      else error ("normal form differs from the default order: " ^ Syntax.string_of_term ctxt t)
    end);
\<close>

lemma "(x::nat) + (z + y) = y + (x + z)" by (simp add: ac_simps)
lemma "(a::int) * (c * b) = b * (a * c)" by (simp add: ac_simps)
lemma "A \<union> (C \<union> B) = B \<union> (A \<union> C)" by (simp add: ac_simps)


section \<open>The comparison must not depend on how a variable is represented\<close>

ML_val \<open>
  val F = Free ("F", @{typ "'a ring"});
  val zeroF = Const (@{const_name Ring.ring.zero}, @{typ "'a ring \<Rightarrow> 'a"}) $ F;
  val fixed = Free ("a", @{typ 'a});
  val bound = Free (Name.bound 0, @{typ 'a});   (*what the simplifier uses under a binder*)
  val _ =
    Ring_Term_Ord.term_ord (zeroF, fixed) = Ring_Term_Ord.term_ord (zeroF, bound)
      orelse error "zero F compares differently against a fixed and a bound variable";
\<close>


section \<open>Goals the algebra method proves, now by plain simp with the locale simprules\<close>

text \<open>Taken from the uses of @{method algebra} in HOL-Algebra.\<close>

lemma (in ring) assumes "a \<in> carrier R" "b \<in> carrier R" shows "a \<ominus> (a \<ominus> b) = b"
  using assms by (simp add: ring_simprules)

lemma (in domain)
  assumes "a \<otimes> b = a \<otimes> c" "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "a \<otimes> (b \<ominus> c) = \<zero>"
  using assms by (simp add: cring_simprules)

lemma (in cring)
  assumes "(a \<otimes> b = a \<otimes> c) = (b = c)" "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "(b \<otimes> a = c \<otimes> a) = (b = c)"
  using assms by (simp add: cring_simprules)

lemma (in ring)
  assumes "hz \<in> carrier R" "hx \<in> carrier R" "hy \<in> carrier R" "x \<in> carrier R" "y \<in> carrier R"
  shows "hz \<oplus> ((hx \<oplus> x) \<otimes> (hy \<oplus> y)) = (hz \<oplus> (hx \<otimes> (hy \<oplus> y)) \<oplus> x \<otimes> hy) \<oplus> x \<otimes> y"
  using assms by (simp add: ring_simprules)

lemma (in cring)
  assumes "\<one> = r \<otimes> a \<oplus> i" "r \<in> carrier R" "a \<in> carrier R" "i \<in> carrier R"
  shows "a \<otimes> r = \<ominus> i \<oplus> \<one>"
  using assms by (simp add: cring_simprules)

lemma (in ring)
  assumes "i \<in> carrier R" "j \<in> carrier R" "a \<in> carrier R" "b \<in> carrier R"
  shows "(i \<oplus> a) \<otimes> (j \<oplus> b) = (i \<oplus> a) \<otimes> j \<oplus> (i \<otimes> b) \<oplus> (a \<otimes> b)"
  using assms by (simp add: ring_simprules)

lemma (in ring)
  assumes "u1 = k1 \<otimes> a \<oplus> v1" "u2 = k2 \<otimes> a \<oplus> v2"
    "k1 \<in> carrier R" "v1 \<in> carrier R" "k2 \<in> carrier R" "v2 \<in> carrier R" "a \<in> carrier R"
  shows "u1 \<oplus> u2 = ((k1 \<oplus> k2) \<otimes> a) \<oplus> (v1 \<oplus> v2)"
  using assms by (simp add: ring_simprules)

lemma (in ring)
  assumes "x \<in> carrier R" "y \<in> carrier R" "x = y"
  shows "x \<oplus> ((\<ominus> \<one>) \<otimes> y) = \<zero>"
  using assms by (simp add: ring_simprules)

lemma (in ring)
  assumes "e \<in> carrier R" "x \<in> carrier R" "f \<in> carrier R" "a \<in> carrier R" "b \<in> carrier R"
  shows "(((e \<otimes> x) \<oplus> f) \<otimes> a) \<oplus> b = (e \<otimes> (x \<otimes> a)) \<oplus> ((f \<otimes> a) \<oplus> b)"
  using assms by (simp add: ring_simprules)

lemma (in ring)
  assumes "x \<in> carrier R" "y \<in> carrier R"
  shows "x = \<ominus> y \<oplus> (y \<oplus> x)"
  using assms by (simp add: ring_simprules)

lemma (in cring)
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "(a \<ominus> b) \<otimes> (a \<oplus> b) = a \<otimes> a \<ominus> b \<otimes> b"
  using assms by (simp add: cring_simprules)

lemma (in ring)
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "f (a \<oplus> (b \<oplus> \<ominus> a)) = f b"
  using assms by (simp add: ring_simprules)

lemma (in ring)
  assumes "a \<in> carrier R"
  shows "a \<oplus> \<zero> = a"
  using assms a_comm l_zero by (simp add: zero_closed del: l_zero r_zero)

end
