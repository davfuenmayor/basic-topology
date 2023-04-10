theory compactness
  imports relativization
begin

(**The "finite intersection property" (FIP)*)
definition "FIP S \<equiv> \<forall>D. nonEmpty D \<and> D \<sqsubseteq> S \<and> finite D \<longrightarrow> \<not>(\<^bold>\<And>D \<approx> \<^bold>\<bottom>)"
(**It can be shown that for meet-closed collections FIP is equivalent to the following "binary intersection property" (BIP)*)
definition "BIP S \<equiv> \<forall>A B. S A \<and> S B \<longrightarrow> \<not>(A \<^bold>\<and> B \<approx> \<^bold>\<bottom>)"
(**Both definitions are equivalent (for meet-closed collections) *)
lemma FBIP_equiv: "meet_closed S \<Longrightarrow> BIP S = FIP S" oops (*Exercise: prove this*)

(**For convenience, we can dualize the FIP towards some sort of "finite union property" (FUP)*)
definition "FUP S \<equiv> \<exists>D. nonEmpty D \<and> D \<sqsubseteq> S \<and> finite D \<and> \<^bold>\<Or>D \<approx> \<^bold>\<top>"
(**and, similarly, the FUP is equivalent to its binary counterpart (BUP) for join-closed collections*)
definition "BUP S \<equiv> \<exists>A B. S A \<and> S B \<and> (A \<^bold>\<or> B \<approx> \<^bold>\<top>)"
(**Both definitions are equivalent (for join-closed collections)*)
lemma FBUP_equiv: "join_closed S \<Longrightarrow> BUP S = FUP S" oops (*Exercise: prove this*)

(**BIP-BUP and FIP-FUP are dual in a sense*)
lemma BIUP_dual1: "(\<not>BIP S) = BUP S\<^sup>-" using BA_deMorgan1 BA_deMorgan2 unfolding BIP_def BUP_def by (smt (z3) BA_dn L13 L14 L2 L4 L5 L9 compl_def dom_compl_def setequ_char setequ_def setequ_equ subset_def)
lemma BIUP_dual2: "(\<not>BUP S) = BIP S\<^sup>-" by (metis BIUP_dual1 dom_compl_invol)

lemma FIUP_dual1: "(\<not>FIP S) = FUP S\<^sup>-" using dom_compl_1to1 finite1to1 by (smt (z3) FIP_def FUP_def bottom_def compl_def dom_compl_def dom_compl_invol iDM_a iDM_b setequ_char top_def)
lemma FIUP_dual2: "(\<not>FUP S) = FIP S\<^sup>-" by (metis FIUP_dual1 dom_compl_invol)

(**Below we can state several definitions of compactness and show them equivalent
 (eventually modulo certain conditions on \<C>). We can also employ BIP/BUP for FIP/FUP.*)

(**The definition of compactness using closed sets*)
definition compact_cl::"('a \<sigma> \<Rightarrow> 'a \<sigma>) \<Rightarrow> bool" ("compact\<^sup>c\<^sup>l")
  where "compact\<^sup>c\<^sup>l \<C> \<equiv> \<forall>S. S \<sqsubseteq> Cl[\<C>] \<and> FIP S \<longrightarrow> \<not>(\<^bold>\<And>S \<approx> \<^bold>\<bottom>)"

(**The more usual (dual) definition using open sets (i.e. 'every open cover has a finite subcover')*)
definition compact_op::"('a \<sigma> \<Rightarrow> 'a \<sigma>) \<Rightarrow> bool" ("compact\<^sup>o\<^sup>p")
  where "compact\<^sup>o\<^sup>p \<C> \<equiv> \<forall>S. S \<sqsubseteq> Op[\<C>] \<and> \<^bold>\<Or>S \<approx> \<^bold>\<top> \<longrightarrow> FUP S"

(**Both definitions above are equivalent (without assuming any condition on \<C>)*)
lemma compact_equiv: "compact\<^sup>c\<^sup>l \<C> = compact\<^sup>o\<^sup>p \<C>" unfolding compact_cl_def compact_op_def by (smt (verit) ClOpdual FIUP_dual1 FIUP_dual2 OpCldual bottom_def compl_def dom_compl_def iDM_a iDM_b setequ_char top_def) 

(*Both the BIP/FIP and BUP/FUP can be stated as relativized wrt. a subspace X*)
definition BIP_rel  ("BIP\<downharpoonleft>\<^sub>_")
  where "BIP\<downharpoonleft>\<^sub>X S \<equiv> \<forall>A B. S A \<and> S B \<longrightarrow> \<not>(X \<^bold>\<and> (A \<^bold>\<and> B) \<approx> \<^bold>\<bottom>)"
definition BUP_rel  ("BUP\<downharpoonleft>\<^sub>_")
  where "BUP\<downharpoonleft>\<^sub>X S \<equiv> \<exists>A B. S A \<and> S B \<and> (X \<preceq> A \<^bold>\<or> B)"

definition FIP_rel  ("FIP\<downharpoonleft>\<^sub>_")
  where "FIP\<downharpoonleft>\<^sub>X S \<equiv> \<forall>D. nonEmpty D \<and> D \<sqsubseteq> S \<and> finite D \<longrightarrow> \<not>(X \<^bold>\<and> \<^bold>\<And>D \<approx> \<^bold>\<bottom>)"
definition FUP_rel  ("FUP\<downharpoonleft>\<^sub>_")
  where "FUP\<downharpoonleft>\<^sub>X S \<equiv> \<exists>D. nonEmpty D \<and> D \<sqsubseteq> S \<and> finite D \<and> (X \<preceq> \<^bold>\<Or>D)"

(**BIP-BUP and FIP-FUP are also dual. Exercise: prove this*)
lemma BIUP_rel_dual1: "(\<not>BIP\<downharpoonleft>\<^sub>X S) = BUP\<downharpoonleft>\<^sub>X S\<^sup>-" sorry
lemma BIUP_rel_dual2: "(\<not>BUP\<downharpoonleft>\<^sub>X S) = BIP\<downharpoonleft>\<^sub>X S\<^sup>-" sorry
lemma FIUP_rel_dual1: "(\<not>FIP\<downharpoonleft>\<^sub>X S) = FUP\<downharpoonleft>\<^sub>X S\<^sup>-" sorry
lemma FIUP_rel_dual2: "(\<not>FUP\<downharpoonleft>\<^sub>X S) = FIP\<downharpoonleft>\<^sub>X S\<^sup>-" sorry

(*Using the relativized definitions above we can define compactness for (sub)spaces and show them equivalent*)

(**The definition of compactness using closed sets*)
definition compactSet_cl::"('a \<sigma> \<Rightarrow> 'a \<sigma>) \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("compactSet\<^sup>c\<^sup>l")
  where "compactSet\<^sup>c\<^sup>l \<C> X \<equiv> \<forall>S. S \<sqsubseteq> Cl[\<C>] \<and> FIP\<downharpoonleft>\<^sub>X S \<longrightarrow> \<not>(X \<^bold>\<and> \<^bold>\<And>S \<approx> \<^bold>\<bottom>)"

(**The more usual (dual) definition using open sets (i.e. 'every open cover has a finite subcover')*)
definition compactSet_op::"('a \<sigma> \<Rightarrow> 'a \<sigma>) \<Rightarrow> 'a \<sigma> \<Rightarrow> bool" ("compactSet\<^sup>o\<^sup>p")
  where "compactSet\<^sup>o\<^sup>p \<C> X \<equiv> \<forall>S. S \<sqsubseteq> Op[\<C>] \<and> X \<preceq> \<^bold>\<Or>S \<longrightarrow> FUP\<downharpoonleft>\<^sub>X S"

(**Both definitions above are equivalent too. 
   Exercise: prove this*)
lemma compactSet_equiv: "compactSet\<^sup>c\<^sup>l \<C> X = compactSet\<^sup>o\<^sup>p \<C> X"  oops

(**Exercise: define and interrelate other definitions of compactness*)
(**Exercise: use compactness to further relate different separation axioms*)

end