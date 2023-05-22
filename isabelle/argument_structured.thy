theory argument_structured
  imports four_logic embedding_basic
begin

type_synonym \<alpha> = "w \<Rightarrow> \<tau>" (*type for structured arguments*)

(*Observe that pairs of booleans have an alternative, simpler representation *)
lemma mkPair_setdef: "\<langle>a,b\<rangle> = (\<lambda>X. (a \<inter> (\<lambda>w. \<not>X)) \<union> (b \<inter> (\<lambda>w. X)))" 
  unfolding connSet  by (metis (mono_tags, opaque_lifting) base.fst_def base.snd_def fst_prop snd_prop)

abbreviation "Support a \<equiv> fst (a\<^sup>T)"
abbreviation "Claim a \<equiv> snd (a\<^sup>T)"
lemma arg_char: "a = \<langle>Support a, Claim a\<rangle>\<^sup>T" by simp

named_theorems argDefs1
named_theorems argDefs2

(** deductive arguments *)
definition \<D>::"\<alpha> Set" where "\<D> \<equiv> \<lambda>A. [Support A \<^bold>\<turnstile> Claim A]"
(** consistent arguments *)
definition \<C>::"\<alpha> Set" where "\<C> \<equiv> \<lambda>A. [\<^bold>\<turnstile>\<^sup>s\<^sup>a\<^sup>t Support A, Claim A]"
(** premise-consistent arguments *)
definition \<C>'::"\<alpha> Set" where "\<C>' \<equiv> \<lambda>A. [\<^bold>\<turnstile>\<^sup>s\<^sup>a\<^sup>t Support A]"

declare \<D>_def[argDefs1] \<C>_def[argDefs1] \<C>'_def[argDefs1]

lemma \<D>_def2: "\<D> A = (\<forall>w. A w \<noteq> \<^bold>F)" by (smt (verit, del_insts) \<D>_def Fval_def mkPair_def mkPair_prop subset_def)
lemma \<C>_def2:  "\<C> A = (\<exists>w. A w = \<^bold>B)" by (smt (verit, del_insts) Bval_def \<C>_def fst_def snd_def eqset_def2 fst_prop inter_def mkPair_prop snd_prop subset_def)
lemma \<C>'_def2: "\<C>' A = (\<exists>w. A w = \<^bold>B \<or> A w = \<^bold>F)" by (smt (verit) \<C>'_def \<C>_def \<C>_def2 \<D>_def \<D>_def2 eqset_def inter_def subset_def)

declare \<D>_def2[argDefs2] \<C>_def2[argDefs2] \<C>'_def2[argDefs2]

lemma \<D>\<C>prop: "\<D> a \<longrightarrow> (\<C>' a = \<C> a)" unfolding argDefs2 by simp

definition \<V>::"\<alpha> Set" where "\<V> \<equiv> \<C> \<inter> \<D>" (** valid/correct arguments *)
definition \<E>::"\<alpha> Set" where "\<E> \<equiv> \<C> \<leftharpoonup> \<D>" (** enthymemes *)
definition \<T>::"\<alpha> Set" where "\<T> \<equiv> \<D> \<leftharpoonup> \<C>" (** trivial arguments *)
definition \<I>::"\<alpha> Set" where "\<I> \<equiv> \<midarrow>(\<C> \<union> \<D>)" (** invalid/self-rebutting arguments *)

declare \<V>_def[argDefs1] \<E>_def[argDefs1] \<T>_def[argDefs1] \<I>_def[argDefs1]

lemma partition: "\<forall>w. \<V> w \<or> \<E> w \<or> \<T> w \<or> \<I> w" unfolding \<E>_def \<I>_def \<T>_def \<V>_def connSet by blast

lemma \<T>_char: "\<T> = \<midarrow>\<C>'" unfolding \<T>_def connSet argDefs2 by blast
lemma \<I>_char: "\<I> = \<C>' \<inter> \<midarrow>\<C>" unfolding \<I>_def connSet argDefs2 by blast

lemma \<V>_def2: "\<V> A = ((\<exists>w. A w = \<^bold>B) \<and> (\<forall>w. A w \<noteq> \<^bold>F))" by (simp add: \<C>_def2 \<D>_def2 \<V>_def connSet) 
lemma \<E>_def2: "\<E> A = ((\<exists>w. A w = \<^bold>B) \<and> (\<exists>w. A w = \<^bold>F))" by (simp add: \<C>_def2 \<D>_def2 \<E>_def diff_def) 
lemma \<T>_def2: "\<T> A = (\<forall>w. A w = \<^bold>N \<or> A w = \<^bold>T)" by (smt (verit, del_insts) Bval_def Fval_def Nval_def Tval_def \<C>'_def2 \<T>_char compl_def fst_prop mkPair_prop)
lemma \<I>_def2: "\<I> A = ((\<forall>w. A w \<noteq> \<^bold>B) \<and> (\<exists>w. A w = \<^bold>F))" by (simp add: \<C>_def2 \<D>_def2 \<I>_def connSet)

(** Three different forms of attack *)
definition undermine::"\<alpha> Rel" ("undermine")
  where "undermine a b \<equiv> [\<^bold>\<turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t Claim a, Support b]"
definition rebute::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" ("rebute")
  where "rebute a b \<equiv> [\<^bold>\<turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t Claim a, Claim b]"
definition undercut::"\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" ("undercut")
  where "undercut a b \<equiv> [\<^bold>\<turnstile> Claim a] \<longrightarrow> \<not>(\<D> b)"

declare undermine_def[argDefs1] rebute_def[argDefs1] undercut_def[argDefs1]

lemma undermine_def2: "undermine a b = (\<forall>w. (a w = \<^bold>B \<or> a w = \<^bold>T) \<longrightarrow> (b w = \<^bold>N \<or> b w = \<^bold>T))"
  by (smt (z3) Bval_def Nval_def Tval_def fst_def snd_def eqset_def fst_prop inter_def mkPair_prop snd_prop undermine_def)
lemma rebute_def2: "rebute a b = (\<forall>w. (a w = \<^bold>B \<or> a w = \<^bold>T) \<longrightarrow> (b w = \<^bold>N \<or> b w = \<^bold>F))"
  by (smt (z3) Bval_def Fval_def Nval_def Tval_def snd_def eqset_def inter_def mkPair_prop rebute_def snd_prop)
lemma undercut_def2: "undercut a b = (\<exists>w. (a w = \<^bold>B \<or> a w = \<^bold>T) \<longrightarrow> b w = \<^bold>F)"
  unfolding undercut_def by (smt (z3) Bval_def \<D>_def2 Tval_def base.snd_def eqset_def mkPair_prop snd_prop )

declare undermine_def2[argDefs2] rebute_def2[argDefs2] undercut_def2[argDefs2]

(*We also introduce the relativized variants (wrt. and universe \<A> of arguments)*)
abbreviation undermine_rel::"\<alpha> Set \<Rightarrow> \<alpha> Rel" ("undermine\<^sup>_")
  where "undermine\<^sup>\<A> a b \<equiv> \<A> a \<and> \<A> b \<and> undermine a b"
abbreviation rebute_rel::"\<alpha> Set\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" ("rebute\<^sup>_")
  where "rebute\<^sup>\<A> a b \<equiv> \<A> a \<and> \<A> b \<and> rebute a b"
abbreviation undercut_rel::"\<alpha> Set\<Rightarrow>\<alpha>\<Rightarrow>\<alpha>\<Rightarrow>bool" ("undercut\<^sup>_")
  where "undercut\<^sup>\<A> a b \<equiv> \<A> a \<and> \<A> b \<and> undercut a b"

(*Rebutting a deductive argument entails undermining it*)
lemma "rebute a b \<and> \<D> b \<longrightarrow> undermine a b" by (smt (verit) \<D>_def eqset_def inter_def rebute_def subset_def undermine_def)

(*The conjunction of the claims of a set of arguments*)
abbreviation "Claims S \<equiv> \<Inter>(\<lambda>C. \<exists>A. S A \<and> (C = Claim A))"
(*The argument-coalition supporting a claim C wrt. a set of arguments S (TODO: useful?)*)
abbreviation supporting::"\<alpha> Set \<Rightarrow> \<sigma> \<Rightarrow> \<alpha>" ("supports")
  where "supporting S C \<equiv> \<langle>Claims S,C\<rangle>\<^sup>T"
lemma "Support (supporting S C) = Claims S" by simp


(*It is in fact possible to define an algebra of arguments. This algebra inherits the structure of FOUR.*)
named_theorems connArg1
named_theorems connArg2

definition meetArg::"\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" (infixr "\<sqinter>\<^sup>a" 80)
  where "A \<sqinter>\<^sup>a B \<equiv> \<lambda>w. A w \<sqinter>\<^sup>4 B w"
definition joinArg::"\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" (infixr "\<squnion>\<^sup>a" 80)
  where "A \<squnion>\<^sup>a B \<equiv> \<lambda>w. A w \<squnion>\<^sup>4 B w"
definition cmplArg::"\<alpha> \<Rightarrow> \<alpha>" ("\<midarrow>\<^sup>a_" 90) (*the complemented argument*)
  where "\<midarrow>\<^sup>aA \<equiv> \<lambda>w. \<midarrow>\<^sup>4(A w)"
definition orderCArg::"\<alpha> Rel" (infixr "\<sqsubseteq>\<^sup>a" 80)
  where "A \<sqsubseteq>\<^sup>a B \<equiv> \<forall>w. A w \<sqsubseteq>\<^sup>4 B w"

declare meetArg_def[connArg1] joinArg_def[connArg1] cmplArg_def[connArg1] orderCArg_def[connArg1]

lemma meetArg_def2: "(A \<sqinter>\<^sup>a B) = \<langle>Support A \<inter> Support B, Claim A \<inter> Claim B\<rangle>\<^sup>T" unfolding connSet connArg1 by s1
lemma joinArg_def2: "(A \<squnion>\<^sup>a B) = \<langle>Support A \<union> Support B, Claim A \<union> Claim B\<rangle>\<^sup>T" unfolding connSet connArg1 by s1
lemma cmplArg_def2: "\<midarrow>\<^sup>aA = \<langle>\<midarrow>(Support A), \<midarrow>(Claim A)\<rangle>\<^sup>T" unfolding connSet connArg1 by s1
lemma order1Arg_def2: "A \<sqsubseteq>\<^sup>a B = (Support A \<subseteq> Support B \<and> Claim A \<subseteq> Claim B)" unfolding connSet connArg1 by s1

declare meetArg_def2[connArg2] joinArg_def2[connArg2] cmplArg_def2[connArg2] order1Arg_def2[connArg2]

definition andArg::"\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" (infixr "\<and>\<^sup>a" 80)
  where "A \<and>\<^sup>a B \<equiv> \<lambda>w. A w \<and>\<^sup>4 B w"
definition orArg::"\<alpha> \<Rightarrow> \<alpha> \<Rightarrow> \<alpha>" (infixr "\<or>\<^sup>a" 80)
  where "A \<or>\<^sup>a B \<equiv> \<lambda>w. A w \<or>\<^sup>4 B w"
definition cnvArg::"\<alpha> \<Rightarrow> \<alpha>" ("\<sim>\<^sup>a_" 90) (*the converse argument*)
  where "\<sim>\<^sup>aA \<equiv> \<lambda>w. \<sim>\<^sup>4(A w)"
definition orderGArg::"\<alpha> Rel" (infixr "\<preceq>\<^sup>a" 80)
  where "A \<preceq>\<^sup>a B \<equiv> \<forall>w. A w \<preceq>\<^sup>4 B w"

declare andArg_def[connArg1] orArg_def[connArg1] cnvArg_def[connArg1] orderGArg_def[connArg1]

lemma andArg_def2: "A \<and>\<^sup>a B = \<langle>Support A \<union> Support B, Claim A \<inter> Claim B\<rangle>\<^sup>T" unfolding connSet connArg1 by s1 
lemma orArg_def2: "A \<or>\<^sup>a B = \<langle>Support A \<inter> Support B, Claim A \<union> Claim B\<rangle>\<^sup>T" unfolding connSet connArg1 by s1 
lemma cnvArg_def2: "\<sim>\<^sup>aA = \<langle>Claim A, Support A\<rangle>\<^sup>T" unfolding connSet connArg1 by s1
(*"B is more general/conservative than A": less demanding on the support and less specific on the claim*)
lemma orderGArg_def2: "A \<preceq>\<^sup>a B = (Support B \<subseteq> Support A \<and> Claim A \<subseteq> Claim B)" unfolding connSet connArg1 by s1

declare andArg_def2[connArg2] orArg_def2[connArg2] cnvArg_def2[connArg2] orderGArg_def2[connArg2]

(*A is a question-begging argument if its converse is deductive:*)
lemma "\<D>(\<sim>\<^sup>aA) = (Claim A \<subseteq> Support A)" by (simp add: \<D>_def fst_def snd_def mkPair_def cnvArg_def2)
end