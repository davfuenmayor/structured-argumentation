theory base
  imports Main
begin

(*Override Sledgehammer and Nitpick default params (inherited by all downstream theories)*)
declare[[smt_timeout=30]]
sledgehammer_params[isar_proof=false, max_facts=30]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=2]

declare[[show_types]]
declare[[syntax_ambiguity_warning=false]]

(*We hide some Isabelle/HOL constants and notation from the libraries to avoid overloading*)
hide_const(open) Set.subset Set.subset_eq Set.supset Set.supset_eq 
                 Set.union Set.inter Set.image Set.vimage  
                 Set.is_empty Set.member Set.is_singleton
                 Relation.converse Relation.Range Relation.total 
                 Complete_Lattices.Inter Complete_Lattices.Union 
                 List.list.Nil List.list.map 
                 Hilbert_Choice.bijection Fun.comp Transitive_Closure.reflcl
                 Product_Type.fst Product_Type.snd

no_notation (*We don't use anything from the Isabelle library *)
  Set.subset  ("'(\<subset>')") and Set.subset  ("(_/ \<subset> _)" [51, 51] 50) and
  Set.subset_eq  ("'(\<subseteq>')") and Set.subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and
  Set.supset  ("'(\<supset>')") and Set.supset  ("(_/ \<supset> _)" [51, 51] 50) and
  Set.supset_eq  ("'(\<supseteq>')") and Set.supset_eq  ("(_/ \<supseteq> _)" [51, 51] 50) and
  Set.union (infixl "\<union>" 65) and Set.inter (infixl "\<inter>" 70) and
  Complete_Lattices.Inter ("\<Inter>") and Complete_Lattices.Union ("\<Union>")

(*Sets are encoded as predicates (i.e. functions with a bool-type codomain)*)
type_synonym 'a Set = \<open>'a \<Rightarrow> bool\<close>
(*Relations as curried binary functions into a bool-type codomain *)
type_synonym 'a Rel = \<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close>


subsection \<open>Boolean structure\<close>

(*We introduce below some operations on sets which endow them with a Boolean algebra structure.*)
named_theorems connSet

(*Two important 0-ary operations (aka. 'constants'). The "universal" and the "empty" set.*)
abbreviation univ::"'a Set" ("\<UU>")
  where "\<UU> \<equiv> \<lambda>x. True"
abbreviation empty::"'a Set" ("\<emptyset>")
  where "\<emptyset> \<equiv> \<lambda>x. False"

(*Set complement is a unary operation*)
definition compl::"'a Set \<Rightarrow> 'a Set" ("\<midarrow>") (*or type: ('a Set, 'a)\<rho> *)
  where \<open>\<midarrow>A \<equiv> \<lambda>x. \<not>A x\<close>
(*We can also define some binary operations on sets *)
definition inter::"'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set" (infixr "\<inter>" 54) 
  where "A \<inter> B \<equiv> \<lambda>x. A x \<and> B x"
definition union::"'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set" (infixr "\<union>" 53) 
  where "A \<union> B \<equiv> \<lambda>x. A x \<or> B x"
definition impl::"'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set" (infixr "\<rightarrow>" 55) 
  where "A \<rightarrow> B \<equiv> \<lambda>x. A x \<longrightarrow> B x" (** (set-)implication*)
definition diff::"'a Set \<Rightarrow> 'a Set \<Rightarrow> 'a Set" (infixr "\<leftharpoonup>" 55) 
  where "A \<leftharpoonup> B \<equiv> \<lambda>x. A x \<and> \<not>B x" (** (set-)difference*)

declare compl_def[connSet] inter_def[connSet] union_def[connSet]
        impl_def[connSet] diff_def[connSet]

(*Union and intersection can be generalized to the infinitary case (i.e. operating on arbitrary sets of sets)*)
definition biginter::"('a Set)Set \<Rightarrow> 'a Set" ("\<Inter>") 
  where "\<Inter>S \<equiv> \<lambda>x. \<forall>A. S A \<longrightarrow> A x"
definition bigunion:: "('a Set)Set \<Rightarrow> 'a Set" ("\<Union>") 
  where "\<Union>S \<equiv> \<lambda>x. \<exists>A. S A  \<and>  A x"

subsection \<open>Order structure\<close>

(*The algebra of sets is ordered by the standard subset relation, as defined below.*)
definition subset::"('a Set)Rel" (infixr "\<subseteq>" 52) 
  where "A \<subseteq> B \<equiv> \<forall>x. A x \<longrightarrow> B x"
    (*Equality between sets is defined as usual*)
definition eqset::\<open>('a Set)Rel\<close> (infix "\<approx>" 51) 
  where eqset_def: \<open>A \<approx> B \<equiv> \<forall>x. A x \<longleftrightarrow> B x\<close>

declare subset_def[connSet] eqset_def[connSet]

abbreviation (input) supset::"('a Set)Rel" (infixr "\<supseteq>" 52) 
  where "A \<supseteq> B \<equiv> B \<subseteq> A"
abbreviation subset'::\<open>('a Set)Rel\<close> (infix "\<subset>" 52) 
  where \<open>A \<subset> B \<equiv> (A \<subseteq> B) \<and> \<not>(A \<approx> B)\<close>
abbreviation (input) psupset::"('a Set)Rel" (infixr "\<supset>" 52) 
  where "A \<supset> B \<equiv> B \<subset> A"

(*We also introduce some useful relativized variants*)
definition subset_rel::\<open>'a Set \<Rightarrow> ('a Set)Rel\<close> ("_ \<subseteq>\<^sub>_ _")
  where \<open>A \<subseteq>\<^sub>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longrightarrow> B x)\<close>
definition eqset_rel::\<open>'a Set \<Rightarrow> ('a Set)Rel\<close> ("_ \<approx>\<^sub>_ _")
  where \<open>A \<approx>\<^sub>U B \<equiv> \<forall>x. U x \<longrightarrow> (A x \<longleftrightarrow> B x)\<close>

declare subset_rel_def[connSet] eqset_rel_def[connSet]

abbreviation psubset_rel::\<open>'a Set \<Rightarrow> ('a Set)Rel\<close> ("_\<subset>\<^sub>_ _")
  where \<open>A \<subset>\<^sub>U B \<equiv> (A \<subseteq>\<^sub>U B) \<and> \<not>(A \<approx>\<^sub>U B)\<close>

lemma subset_rel_char: "(A \<subseteq>\<^sub>U B) = (U \<inter> A \<subseteq> U \<inter> B)" by (smt (verit, best) inter_def subset_def subset_rel_def)
lemma eqset_rel_char: "(A \<approx>\<^sub>U B) = (U \<inter> A \<approx> U \<inter> B)" by (smt (z3) eqset_def eqset_rel_def inter_def)

(*Some useful equivalences:*)
lemma eqset_def2: "(A \<approx> B) = (A \<subseteq> B \<and> B \<subseteq> A)"
  by (metis (mono_tags, lifting) eqset_def subset_def)
lemma eqset_rel_def2: "(A \<approx>\<^sub>U B) = (A \<subseteq>\<^sub>U B \<and> B \<subseteq>\<^sub>U A)"
  by (simp add: eqset_def2 eqset_rel_char subset_rel_char)
lemma subset_contrapos: "(\<midarrow>B \<subseteq> \<midarrow>A) = (A \<subseteq> B)" 
  by (metis (full_types) compl_def subset_def)
lemma subset_rel_contrapos: "(\<midarrow>B \<subseteq>\<^sub>U \<midarrow>A) = (A \<subseteq>\<^sub>U B)" 
  by (smt (verit) compl_def subset_rel_def)
lemma eqset_ext: "(A \<approx> B) = (A = B)"
  using eqset_def by auto
lemma eqset_rel_ext: "(A \<approx>\<^sub>U B) = ((A \<inter> U) = (B \<inter> U))"
  sorry (*TODO reconstruct*)


subsection \<open>Atoms\<close>

(*(Boolean) algebras of sets are atomic, their atoms being the singleton sets.
  We can easily create singleton sets by partially applying HOL equality *)
abbreviation (input) unitset::"'a \<Rightarrow> 'a Set" ("{_}")
  where \<open>{a} \<equiv> \<lambda>x. x = a\<close>
(* We can extrapolate the above notation to provide some convenient set-builder notation on demand: *)
abbreviation (input) pairset::"'a \<Rightarrow> 'a \<Rightarrow> 'a Set" ("{_,_}")
  where \<open>{a,b} \<equiv> \<lambda>x. x = a \<or> x = b\<close>
abbreviation (input) tripleset::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a Set" ("{_,_,_}")
  where \<open>{a,b,c} \<equiv> \<lambda>x. x = a \<or> x = b \<or> x = c\<close>
(* (add more on demand)*)


subsection \<open>(Endo-)Relations\<close>

(*We define the transpose of an arbitrary binary function as swapping the first and second arguments. 
 Note that the transpose/converse of a relation is just the special case with 'a = 'b and 'c = bool.*)
abbreviation (input) transpose::"('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'a \<Rightarrow> 'c)" ("(_)\<^sup>T" [90])
  where \<open>f\<^sup>T \<equiv> \<lambda>a b. f b a\<close>
abbreviation rel_cluster::"'a Rel \<Rightarrow> 'a Rel" ("_\<^sup>=" [90]) 
  where \<open>R\<^sup>= \<equiv> \<lambda>a b. R a b \<and> R\<^sup>T a b\<close> (* 'undoes' R leaving only R-clusters*)

(*The set of least (resp. greatest) elements of a set A wrt. a relation R*)
definition least::"'a Rel \<Rightarrow> ('a Set \<Rightarrow> 'a Set)" ("_-least")
  where \<open>R-least \<equiv> \<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R m x)\<close>
definition greatest::"'a Rel \<Rightarrow> ('a Set \<Rightarrow> 'a Set)" ("_-greatest")
  where \<open>R-greatest \<equiv> \<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R x m)\<close>

(*The set of minimal (resp. maximal) elements of a set A wrt. a relation R can be defined in two ways:*)
(*(1) Using R-clusters for equality comparison (cycles are possible) *)
definition minimal::"'a Rel \<Rightarrow> ('a Set \<Rightarrow> 'a Set)" ("_-min")
  where \<open>R-min \<equiv> \<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<and> R x m \<longrightarrow> R\<^sup>= x m)\<close>
definition maximal::"'a Rel \<Rightarrow> ('a Set \<Rightarrow> 'a Set)" ("_-max")
  where \<open>R-max \<equiv> \<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<and> R m x \<longrightarrow> R\<^sup>= x m)\<close>
(*(2) Using (=) for comparison (no cycles posible) *)
definition minimal_eq::"'a Rel \<Rightarrow> ('a Set \<Rightarrow> 'a Set)" ("_-min\<^sup>=")
  where \<open>R-min\<^sup>= \<equiv> \<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<and> R x m \<longrightarrow> x = m)\<close>
definition maximal_eq::"'a Rel \<Rightarrow> ('a Set \<Rightarrow> 'a Set)" ("_-max\<^sup>=")
  where \<open>R-max\<^sup>= \<equiv> \<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<and> R m x \<longrightarrow> x = m)\<close>

lemma greatest__least_trans: \<open>R-greatest = R\<^sup>T-least\<close> 
  by (simp add: least_def greatest_def)
lemma max_min_trans:  \<open>R-max = R\<^sup>T-min\<close> 
  unfolding minimal_def maximal_def by simp
lemma max_min_eq_trans:  \<open>R-max\<^sup>= = R\<^sup>T-min\<^sup>=\<close> 
  unfolding minimal_eq_def maximal_eq_def by simp


subsection \<open>Pairs\<close>

type_synonym ('a)Pair = "bool \<Rightarrow> 'a" (*type for pairs*)

definition fst::"'a Pair \<Rightarrow> 'a" ("fst")
  where "fst p \<equiv> p False"
definition snd::"'a Pair \<Rightarrow> 'a" ("snd")
  where "snd p \<equiv> p True"
definition mkPair::"'a \<Rightarrow> 'a \<Rightarrow> 'a Pair" ("\<langle>_,_\<rangle>")
  where "\<langle>A,B\<rangle> \<equiv> \<lambda>X. if X then B else A"

lemma fst_prop[simp]: "fst\<langle>X,Y\<rangle> = X" by (simp add: mkPair_def fst_def)
lemma snd_prop[simp]: "snd\<langle>X,Y\<rangle> = Y" by (simp add: mkPair_def snd_def)
lemma mkPair_prop[simp]: "\<langle>fst X, snd X\<rangle> = X" unfolding mkPair_def fst_def snd_def by fastforce

abbreviation pair_swap::"'a Pair \<Rightarrow> 'a Pair" ("_\<Zcat>")
  where "p\<Zcat> \<equiv> \<langle>snd p, fst p\<rangle>"

definition curry::"('a Pair)Set \<Rightarrow> ('a)Rel" ("\<lfloor>_\<rfloor>"[90])
  where "curry r \<equiv> \<lambda>A B. r\<langle>A,B\<rangle>"
definition uncurry::"('a)Rel \<Rightarrow> ('a Pair)Set"  ("\<lceil>_\<rceil>"[91])
  where "uncurry r \<equiv> \<lambda>p. r (fst p) (snd p)"

lemma curry_prop1[simp]: "\<lceil>\<lfloor>r\<rfloor>\<rceil> = r" by (simp add: curry_def uncurry_def)
lemma curry_prop2[simp]: "\<lfloor>\<lceil>r\<rceil>\<rfloor> = r" by (simp add: curry_def uncurry_def)


subsection \<open>Fixed-points\<close>

(*For a given unary set-operator (mapping sets to sets) returns the set of its fixed-points.*)
abbreviation (input) fp :: \<open>('a Set \<Rightarrow> 'a Set) \<Rightarrow> ('a Set)Set\<close> ("fp")
  where \<open>fp \<phi> \<equiv> \<lambda>S. (\<phi> S) \<approx> S\<close>
abbreviation (input) fp_rel:: \<open>'a Set \<Rightarrow> ('a Set \<Rightarrow> 'a Set) \<Rightarrow> ('a Set)Set\<close> ("fp\<^sup>_")
  where \<open>fp\<^sup>U \<phi> \<equiv> \<lambda>S. (\<phi> S) \<approx>\<^sub>U S\<close>

lemma fp_rel_prop: \<open>fp \<phi> S \<Longrightarrow> fp\<^sup>U \<phi> S\<close> by (simp add: eqset_ext eqset_rel_def)

(*Useful lemma(?)*)
lemma fp_prop1: \<open>(\<forall>U. (\<lambda>X Y. X \<subseteq>\<^sub>U Y)-least (fp\<^sup>U F) S) \<longrightarrow> (\<subseteq>)-least (fp F) S\<close>
  unfolding least_def by (metis (mono_tags, opaque_lifting) eqset_def2 eqset_rel_def fp_rel_prop subset_def subset_rel_def) 

(* Definition of a monotone function (wrt. an universe U).*)
definition MONO::"('a Set \<Rightarrow> 'b Set) \<Rightarrow> bool" ("MONO")
  where \<open>MONO F \<equiv> \<forall>A B. A \<subseteq> B \<longrightarrow> F A \<subseteq> F B\<close>
definition MONO_rel::"'a Set \<Rightarrow> ('a Set \<Rightarrow> 'a Set) \<Rightarrow> bool" ("MONO\<^sup>_") 
  where \<open>MONO\<^sup>U F \<equiv> \<forall>A B. (A \<subseteq>\<^sub>U B \<longrightarrow> F A \<subseteq>\<^sub>U F B)\<close>

(* Weak variant of the Knaster-Tarski Theorem (in different formulations):
 Any monotone function on a powerset lattice has a least/greatest fixed-point.*)
lemma wKTl': \<open>MONO F \<Longrightarrow> let S = \<Inter>(\<lambda>X. F X \<subseteq> X) in ((\<subseteq>)-least (fp F) S)\<close> unfolding least_def MONO_def biginter_def by (smt (verit, best) eqset_def2 subset_def) 
lemma wKTg': \<open>MONO F \<Longrightarrow> let S = \<Union>(\<lambda>X. X \<subseteq> F X) in ((\<subseteq>)-greatest (fp F) S)\<close> unfolding greatest_def MONO_def bigunion_def by (smt (verit, del_insts) eqset_def2 subset_def)
lemma wKTl:  \<open>MONO F \<Longrightarrow> \<exists>S. (\<subseteq>)-least (fp F) S\<close> using wKTl' by auto
lemma wKTg:  \<open>MONO F \<Longrightarrow> \<exists>S. (\<subseteq>)-greatest (fp F) S\<close> using wKTg' by auto

lemma wKTl_rel': \<open>MONO\<^sup>U F \<Longrightarrow> let S = \<Inter>(\<lambda>X. F X \<subseteq>\<^sub>U X) in ((\<subseteq>)-least (fp\<^sup>U F) S)\<close> unfolding MONO_rel_def least_def biginter_def subset_rel_def eqset_rel_def subset_def by (smt (z3))
lemma wKTg_rel': \<open>MONO\<^sup>U F \<Longrightarrow> let S = \<Union>(\<lambda>X. X \<subseteq>\<^sub>U F X) in ((\<subseteq>)-greatest (fp\<^sup>U F) S)\<close>  unfolding MONO_rel_def greatest_def bigunion_def subset_rel_def eqset_rel_def subset_def by (smt (z3))

lemma wKTl_rel: \<open>MONO\<^sup>U F \<Longrightarrow> \<exists>S. (\<subseteq>)-least (fp\<^sup>U F) S\<close> using wKTl_rel' by auto
lemma wKTl_relw: \<open>MONO\<^sup>U F \<Longrightarrow> \<exists>S. (\<lambda>X Y. X \<subseteq>\<^sub>U Y)-least (fp\<^sup>U F) S\<close> using wKTl_rel by (smt (verit, del_insts) least_def subset_def subset_rel_def)
lemma wKTg_rel: \<open>MONO\<^sup>U F \<Longrightarrow> \<exists>S. (\<subseteq>)-greatest (fp\<^sup>U F) S\<close> using wKTg_rel' by auto
lemma wKTg_relw: \<open>MONO\<^sup>U F \<Longrightarrow> \<exists>S. (\<lambda>X Y. X \<subseteq>\<^sub>U Y)-greatest (fp\<^sup>U F) S\<close> using wKTg_rel by (smt (verit, del_insts) greatest_def subset_def subset_rel_def)

end