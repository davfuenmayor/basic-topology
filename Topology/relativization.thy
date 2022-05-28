theory relativization
  imports properties
begin

(**When working with closure operators the notion of relativization plays 
an analogous role to that of a subspace.*)

(**We can relativize a closure operator wrt. a subset S of its carrier (implicitly given as 'a-type domain)*)
definition relativization::"('w \<sigma>, 'w \<sigma>)\<phi> \<Rightarrow> 'w \<sigma> \<Rightarrow> ('w \<sigma>, 'w \<sigma>)\<phi>" ("_\<downharpoonleft>\<^sub>_")
  where "\<C>\<downharpoonleft>\<^sub>S \<equiv> \<lambda>A. S \<^bold>\<and> \<C> A"

(**Kuratowski conditions (like additivity, normality, idempotence, etc)
 can be relativized wrt. to a given subset S of the space.*)

definition ADDI_rel::"'w \<sigma> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("ADDI\<downharpoonleft>\<^sub>_")
  where "ADDI\<downharpoonleft>\<^sub>S \<phi> \<equiv> \<forall>A B. S \<^bold>\<and> \<phi>(A \<^bold>\<or> B) \<^bold>\<approx> (S \<^bold>\<and> \<phi> A) \<^bold>\<or> (S \<^bold>\<and> \<phi> B)"
definition EXPN_rel::"'w \<sigma> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("EXPN\<downharpoonleft>\<^sub>_")
  where "EXPN\<downharpoonleft>\<^sub>S \<phi>  \<equiv> \<forall>A. S \<^bold>\<and> A \<^bold>\<preceq> S \<^bold>\<and> \<phi> A"
definition NORM_rel::"'w \<sigma> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("NORM\<downharpoonleft>\<^sub>_")
  where "NORM\<downharpoonleft>\<^sub>S \<phi>  \<equiv> S \<^bold>\<and> (\<phi> \<^bold>\<bottom>) \<^bold>\<approx> S \<^bold>\<and> \<^bold>\<bottom>"
definition IDEM_rel::"'w \<sigma> \<Rightarrow> ('w \<sigma>,'w \<sigma>)\<phi> \<Rightarrow> bool" ("IDEM\<downharpoonleft>\<^sub>_") 
  where "IDEM\<downharpoonleft>\<^sub>S \<phi>  \<equiv> \<forall>A. S \<^bold>\<and> (\<phi> A) \<^bold>\<approx> S \<^bold>\<and> \<phi>(S \<^bold>\<and> \<phi> A)"

abbreviation Cl_1_rel ("Cl'_1\<downharpoonleft>\<^sub>_") where "Cl_1\<downharpoonleft>\<^sub>S \<phi> \<equiv> (ADDI\<downharpoonleft>\<^sub>S) \<phi>"
abbreviation Cl_2_rel ("Cl'_2\<downharpoonleft>\<^sub>_") where "Cl_2\<downharpoonleft>\<^sub>S \<phi> \<equiv> (EXPN\<downharpoonleft>\<^sub>S) \<phi>"
abbreviation Cl_3_rel ("Cl'_3\<downharpoonleft>\<^sub>_") where "Cl_3\<downharpoonleft>\<^sub>S \<phi> \<equiv> (NORM\<downharpoonleft>\<^sub>S) \<phi>"
abbreviation Cl_4_rel ("Cl'_4\<downharpoonleft>\<^sub>_") where "Cl_4\<downharpoonleft>\<^sub>S \<phi> \<equiv> (IDEM\<downharpoonleft>\<^sub>S) \<phi>"

(**We show that relativized closure operators satisfy the relativized Kuratowski conditions*)
lemma "Cl_1 \<C> \<longrightarrow> Cl_1\<downharpoonleft>\<^sub>S \<C>\<downharpoonleft>\<^sub>S" by (simp add: ADDI_def ADDI_rel_def BA_distr1 relativization_def setequ_equ)
lemma "Cl_2 \<C> \<longrightarrow> Cl_2\<downharpoonleft>\<^sub>S \<C>\<downharpoonleft>\<^sub>S" by (metis (mono_tags, lifting) EXPN_def EXPN_rel_def L12 L2 L4 relativization_def) 
lemma "Cl_3 \<C> \<longrightarrow> Cl_3\<downharpoonleft>\<^sub>S \<C>\<downharpoonleft>\<^sub>S" by (metis L14 L5 NORM_def NORM_rel_def relativization_def setequ_equ)
lemma "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4 \<C> \<longrightarrow> Cl_4\<downharpoonleft>\<^sub>S \<C>\<downharpoonleft>\<^sub>S" unfolding MONO_def EXPN_def IDEM_rel_def IDEM_def by (smt (verit, best) L10 L12 L3 L4 L5 antisymmetric_def reflexive_def relativization_def setequ_equ subset_antisymmetric subset_reflexive)

(**We need to be careful when defining the dual interior operator for relativised closures,*)
abbreviation Int_cl_rel ("\<I>\<downharpoonleft>\<^sub>_[_]") where "\<I>\<downharpoonleft>\<^sub>S[\<C>] \<equiv> \<lambda>X. S \<^bold>\<leftharpoonup> \<C>(S \<^bold>\<leftharpoonup> X)"
(*and also when defining the notions of closed/open sets.*)
abbreviation closedset_rel ("Cl\<downharpoonleft>\<^sub>_[_]") where "Cl\<downharpoonleft>\<^sub>S[\<C>] \<equiv> Cl[\<C>\<downharpoonleft>\<^sub>S]"
abbreviation openset_rel ("Op\<downharpoonleft>\<^sub>_[_]") where "Op\<downharpoonleft>\<^sub>S[\<C>] \<equiv> fp \<I>\<downharpoonleft>\<^sub>S[\<C>]"

(**A necessary and sufficient condition for a set to be closed relative to S
is that it is to be the intersection of S and of a closed set.*) (*exercise: verify for opens*)
lemma aux1: "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> \<forall>A. (\<exists>E. Cl[\<C>] E \<and> A \<^bold>\<approx> S \<^bold>\<and> E) \<longrightarrow> Cl\<downharpoonleft>\<^sub>S[\<C>] A" unfolding fixpoint_pred_def relativization_def by (metis EXPN_def L12 L3 L4 L5 L8 MONO_def setequ_def setequ_equ) 
lemma aux2: "Cl_4 \<C> \<Longrightarrow> \<forall>A. Cl\<downharpoonleft>\<^sub>S[\<C>] A \<longrightarrow> (\<exists>E. Cl[\<C>] E \<and> A \<^bold>\<approx> S \<^bold>\<and> E)" unfolding fixpoint_pred_def relativization_def by (metis IDEM_def setequ_equ)
lemma "MONO \<C> \<Longrightarrow> Cl_2 \<C> \<Longrightarrow> Cl_4 \<C> \<Longrightarrow> \<forall>A. Cl\<downharpoonleft>\<^sub>S[\<C>] A \<longleftrightarrow> (\<exists>E. Cl[\<C>] E \<and> A \<^bold>\<approx> S \<^bold>\<and> E)" 
  using aux1 aux2 by blast

(*In particular, if S is closed, then the property of being closed relative to S
 implies the same property in the absolute sense.*)  (*exercise: verify for opens*)
lemma "MONO \<C> \<Longrightarrow> Cl[\<C>] S \<longrightarrow> Cl\<downharpoonleft>\<^sub>S[\<C>] \<sqsubseteq> Cl[\<C>]" by (metis (full_types) L10 L4 MONO_def fixpoint_pred_def relativization_def setequ_equ)

(*Being relatively closed is transitive: if A is closed in B and B is closed in C
 then A is closed in C (same for open)*) (*exercise: verify for opens*)
lemma "MONO \<C> \<Longrightarrow> \<forall>A B C. Cl\<downharpoonleft>\<^sub>B[\<C>] A \<and> Cl\<downharpoonleft>\<^sub>C[\<C>] B \<longrightarrow> Cl\<downharpoonleft>\<^sub>C[\<C>] A" 
  unfolding relativization_def by (smt (z3) L10 MONO_def fixpoint_pred_def meet_def setequ_char setequ_equ)

(**Above we have seen that the Kuratowski axioms can be relativized wrt. an arbitrary subset S of the space.
Consequently the same applies to the theorems which follow from these axioms; they remain valid if 
one considers an arbitrary subspace S and the closure is relativized wrt. S as shown above. Exercise: prove some. *)

(**Many topological properties are preserved when relativizing (dense, nowhere-dense, etc). Exercise: prove some*)

end