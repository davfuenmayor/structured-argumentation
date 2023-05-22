theory four_logic
  imports base "HOL-Eisbach.Eisbach"
begin

section \<open>bilattice-based 4-valued-logic (FOUR)\<close>

type_synonym \<tau> = "(bool)Pair" (* type for 4-valued truth values*)

(*The 4 possible values of type \<tau> *)
definition Tval ("\<^bold>T") where "\<^bold>T \<equiv> \<langle>False,True\<rangle>"
definition Fval ("\<^bold>F") where "\<^bold>F \<equiv> \<langle>True,False\<rangle>"
definition Bval ("\<^bold>B") where "\<^bold>B \<equiv> \<langle>True,True\<rangle>"
definition Nval ("\<^bold>N") where "\<^bold>N \<equiv> \<langle>False,False\<rangle>"

named_theorems val4
declare Tval_def[val4] Fval_def[val4] Bval_def[val4] Nval_def[val4]

(*Observe that pairs of booleans have an alternative, simpler representation *)
lemma mkPair_booldef: "\<langle>a,b\<rangle> = (\<lambda>X. (a \<and> \<not>X) \<or> (b \<and> X))" by (metis mkPair_def)

lemma Tval_def2: "\<^bold>T = (\<lambda>x. x)" by (simp add: Tval_def mkPair_booldef)
lemma Fval_def2: "\<^bold>F = (\<lambda>x. \<not>x)" by (simp add: Fval_def mkPair_booldef)
lemma Bval_def2: "\<^bold>B = (\<lambda>x. True)" by (simp add: Bval_def mkPair_booldef)
lemma Nval_def2: "\<^bold>N = (\<lambda>x. False)" by (simp add: Nval_def mkPair_booldef)

(*The set FOUR := {\<^bold>T,\<^bold>F,\<^bold>B,\<^bold>N} is a bilattice. It has two sets of lattice operations.*)
named_theorems conn4

(*The first set of operations form a so-called 'approximation lattice' A4 *)
definition meetA4::"\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<sqinter>\<^sup>4" 80)
  where "a \<sqinter>\<^sup>4 b \<equiv> \<langle>fst a \<and> fst b, snd a \<and> snd b\<rangle>"
definition joinA4::"\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<squnion>\<^sup>4" 80)
  where "a \<squnion>\<^sup>4 b \<equiv> \<langle>fst a \<or> fst b, snd a \<or> snd b\<rangle>"
definition cmplA4::"\<tau> \<Rightarrow> \<tau>" ("\<midarrow>\<^sup>4_" 90)
  where "\<midarrow>\<^sup>4a \<equiv> \<langle>\<not>(fst a), \<not>(snd a)\<rangle>"

definition orderA4::"\<tau> Rel" (infixr "\<sqsubseteq>\<^sup>4" 80)
  where "a \<sqsubseteq>\<^sup>4 b \<equiv> (fst a \<longrightarrow> fst b) \<and> (snd a \<longrightarrow> snd b)"

declare meetA4_def[conn4] joinA4_def[conn4] cmplA4_def[conn4] orderA4_def[conn4]

(*We introduce two custom solvers:
 (s1) is fast and works well for goals involving meets & joins with complement
 (s2) is slower and works well for (most of) the rest *)
method s1 = unfold conn4; auto simp add: mkPair_def fst_def snd_def val4
method s2 = unfold conn4; (smt (verit, del_insts) fst_prop snd_prop mkPair_prop val4)

lemma orderA4_def2:  "(a \<sqsubseteq>\<^sup>4 b) = (a = a \<sqinter>\<^sup>4 b)" by s2
lemma orderA4_def3:  "(a \<sqsubseteq>\<^sup>4 b) = (b = a \<squnion>\<^sup>4 b)" by s2

(*We verify the intended 'Hasse diagram' for A4*)
lemma "\<^bold>T \<sqinter>\<^sup>4 \<^bold>F = \<^bold>N" by s1
lemma "\<^bold>B \<sqinter>\<^sup>4 \<^bold>N = \<^bold>N" by s1
lemma "\<^bold>B \<sqinter>\<^sup>4 \<^bold>T = \<^bold>T" by s1
lemma "\<^bold>B \<sqinter>\<^sup>4 \<^bold>F = \<^bold>F" by s1
lemma "\<^bold>T \<sqinter>\<^sup>4 \<^bold>N = \<^bold>N" by s1
lemma "\<^bold>F \<sqinter>\<^sup>4 \<^bold>N = \<^bold>N" by s1

lemma "\<^bold>B \<squnion>\<^sup>4 \<^bold>N = \<^bold>B" by s1
lemma "\<^bold>B \<squnion>\<^sup>4 \<^bold>T = \<^bold>B" by s1
lemma "\<^bold>B \<squnion>\<^sup>4 \<^bold>F = \<^bold>B" by s1
lemma "\<^bold>T \<squnion>\<^sup>4 \<^bold>F = \<^bold>B" by s1
lemma "\<^bold>T \<squnion>\<^sup>4 \<^bold>N = \<^bold>T" by s1
lemma "\<^bold>F \<squnion>\<^sup>4 \<^bold>N = \<^bold>F" by s1

lemma "\<midarrow>\<^sup>4\<^bold>T = \<^bold>F" by s1
lemma "\<midarrow>\<^sup>4\<^bold>B = \<^bold>N" by s1

(*Distributivity*)
lemma A4_distr1: "(a \<sqinter>\<^sup>4 (b \<squnion>\<^sup>4 c)) = ((a \<sqinter>\<^sup>4 b) \<squnion>\<^sup>4 (a \<sqinter>\<^sup>4 c))" by s1
lemma A4_distr2: "(a \<squnion>\<^sup>4 (b \<sqinter>\<^sup>4 c)) = ((a \<squnion>\<^sup>4 b) \<sqinter>\<^sup>4 (a \<squnion>\<^sup>4 c))" by s1

(*Negation properties: involutivity, de Morgan law, contraposition*)
lemma cmplA4_invol: "\<midarrow>\<^sup>4\<midarrow>\<^sup>4a = a" by s2
lemma cmplA4_DM1: "\<midarrow>\<^sup>4(a \<squnion>\<^sup>4 b) = ((\<midarrow>\<^sup>4a) \<sqinter>\<^sup>4 (\<midarrow>\<^sup>4b))" by s1
lemma cmplA4_DM2: "\<midarrow>\<^sup>4(a \<sqinter>\<^sup>4 b) = ((\<midarrow>\<^sup>4a) \<squnion>\<^sup>4 (\<midarrow>\<^sup>4b))" by s1
lemma cmplA4_cp1: "a \<sqsubseteq>\<^sup>4 b \<longleftrightarrow> \<midarrow>\<^sup>4b \<sqsubseteq>\<^sup>4 \<midarrow>\<^sup>4a" by s2
lemma cmplA4_cp2: "a \<sqsubseteq>\<^sup>4 \<midarrow>\<^sup>4b \<longleftrightarrow> b \<sqsubseteq>\<^sup>4 \<midarrow>\<^sup>4a" by s1

(*The second set of operations form a so-called 'logical lattice' L4 *)
definition meetL4::"\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<and>\<^sup>4" 80)
  where "A \<and>\<^sup>4 B \<equiv> \<langle>fst A \<or> fst B, snd A \<and> snd B\<rangle>"
definition joinL4::"\<tau> \<Rightarrow> \<tau> \<Rightarrow> \<tau>" (infixr "\<or>\<^sup>4" 80)
  where "A \<or>\<^sup>4 B \<equiv> \<langle>fst A \<and> fst B, snd A \<or> snd B\<rangle>"
definition cmplL4::"\<tau> \<Rightarrow> \<tau>" ("\<sim>\<^sup>4_" 90)
  where "\<sim>\<^sup>4A \<equiv> A\<Zcat>"

definition orderL4::"\<tau> Rel" (infixr "\<preceq>\<^sup>4" 80)
  where "A \<preceq>\<^sup>4 B \<equiv> (fst B \<longrightarrow> fst A) \<and> (snd A \<longrightarrow> snd B)"

declare meetL4_def[conn4] joinL4_def[conn4] cmplL4_def[conn4] orderL4_def[conn4]

lemma orderL4_def2:  "(A \<preceq>\<^sup>4 B) = (A = A \<and>\<^sup>4 B)" by s2
lemma orderL4_def3:  "(A \<preceq>\<^sup>4 B) = (B = A \<or>\<^sup>4 B)" by s2

(*We verify the intended 'Hasse diagram' for L4*)
lemma "(\<^bold>T \<and>\<^sup>4 \<^bold>F) = \<^bold>F" by s1
lemma "(\<^bold>N \<and>\<^sup>4 \<^bold>B) = \<^bold>F" by s1
lemma "(\<^bold>T \<and>\<^sup>4 \<^bold>N) = \<^bold>N" by s1
lemma "(\<^bold>T \<and>\<^sup>4 \<^bold>B) = \<^bold>B" by s1
lemma "(\<^bold>N \<and>\<^sup>4 \<^bold>F) = \<^bold>F" by s1
lemma "(\<^bold>B \<and>\<^sup>4 \<^bold>F) = \<^bold>F" by s1

lemma "(\<^bold>T \<or>\<^sup>4 \<^bold>F) = \<^bold>T" by s1
lemma "(\<^bold>T \<or>\<^sup>4 \<^bold>N) = \<^bold>T" by s1
lemma "(\<^bold>T \<or>\<^sup>4 \<^bold>B) = \<^bold>T" by s1
lemma "(\<^bold>N \<or>\<^sup>4 \<^bold>B) = \<^bold>T" by s1
lemma "(\<^bold>N \<or>\<^sup>4 \<^bold>F) = \<^bold>N" by s1
lemma "(\<^bold>B \<or>\<^sup>4 \<^bold>F) = \<^bold>B" by s1

lemma "\<sim>\<^sup>4\<^bold>F = \<^bold>T" by s1
lemma "\<sim>\<^sup>4\<^bold>N = \<^bold>N" by s1
lemma "\<sim>\<^sup>4\<^bold>B = \<^bold>B" by s1

(*Distributivity*)
lemma L4_distr1: "(a \<and>\<^sup>4 (b \<or>\<^sup>4 c)) = ((a \<and>\<^sup>4 b) \<or>\<^sup>4 (a \<and>\<^sup>4 c))" by s1
lemma L4_distr2: "(a \<or>\<^sup>4 (b \<and>\<^sup>4 c)) = ((a \<or>\<^sup>4 b) \<and>\<^sup>4 (a \<or>\<^sup>4 c))" by s1

(*Negation properties: involutivity, de Morgan law, contraposition*)
lemma cmplL4_invol: "\<sim>\<^sup>4\<sim>\<^sup>4a = a" by s2
lemma cmplL4_DM1: "\<sim>\<^sup>4(a \<or>\<^sup>4 b) = ((\<sim>\<^sup>4a) \<and>\<^sup>4 (\<sim>\<^sup>4b))" by s1
lemma cmplL4_DM2: "\<sim>\<^sup>4(a \<and>\<^sup>4 b) = ((\<sim>\<^sup>4a) \<or>\<^sup>4 (\<sim>\<^sup>4b))" by s1
lemma cmplL4_cp1: "a \<preceq>\<^sup>4 b \<longleftrightarrow> \<sim>\<^sup>4b \<preceq>\<^sup>4 \<sim>\<^sup>4a" by s1
lemma cmplL4_cp2: "a \<preceq>\<^sup>4 \<sim>\<^sup>4b \<longleftrightarrow> b \<preceq>\<^sup>4 \<sim>\<^sup>4a" by s1

end