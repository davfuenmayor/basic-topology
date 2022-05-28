theory properties
  imports "../TBAs/closure_algebra"
begin

(**We investigate some well known topological properties of sets drawing upon closure algebras.*)

(**Sets with an empty interior are called boundary.*)
definition boundary ("boundary[_]") 
  where "boundary[\<C>] A \<equiv> \<I>[\<C>] A \<^bold>\<approx> \<^bold>\<bottom>"

(**Boundary sets can be equivalently defined as the fixed points of the border operator.*)
lemma boundary_def2: "Cl_2 \<C> \<Longrightarrow> boundary[\<C>] = Br[\<C>]" by (simp add: Br_Iempty boundary_def ext)

(**Sets whose closure is the whole domain are called dense.*)
definition dense ("dense[_]") 
  where "dense[\<C>] A \<equiv> \<C> A \<^bold>\<approx> \<^bold>\<top>"

(**A set is dense iff its complement is boundary.*)
lemma dense_def2: "dense[\<C>] A = boundary[\<C>] (\<^bold>\<midarrow>A)" unfolding dense_def boundary_def by (simp add: bottom_def compl_def op_dual_def setequ_char top_def)
(**Dense sets can be equivalently defined as the fixed points of the dual-border operator.*)
lemma dense_def3: "Cl_2 \<C> \<Longrightarrow> dense[\<C>] = fp (\<B>[\<C>])\<^sup>d" by (metis (full_types) boundary_def2 dense_def2 fp3 fp_d op_equal_equ setequ_char setequ_equ)


(**Sets whose closure is a boundary set are called nowhere-dense.*)
definition nowhereDense ("nowhereDense[_]") 
  where "nowhereDense[\<C>] A \<equiv> boundary[\<C>] (\<C> A)"

(**For closed sets the properties of boundary and nowhere-dense collapse.*)
lemma Cl_bnd_nwdn: "\<forall>A. Cl[\<C>] A \<longrightarrow> boundary[\<C>] A = nowhereDense[\<C>] A" by (simp add: fixpoint_pred_def nowhereDense_def setequ_equ)

(**Let us introduce a definition for the sets mentioned above (nowhere-dense and closed).*)
definition nowhereDenseCl ("nowhereDenseCl[_]") 
  where "nowhereDenseCl[\<C>] A \<equiv> nowhereDense[\<C>] A \<and> Cl[\<C>] A"

(**A set is nowhere-dense and closed iff its complement is dense and open.*)
lemma nowhereDenseCl_def2: "nowhereDenseCl[\<C>] A = (dense[\<C>] (\<^bold>\<midarrow>A) \<and> Op[\<C>] (\<^bold>\<midarrow>A))" by (metis BA_dn Cl_bnd_nwdn OpCldual dense_def2 nowhereDenseCl_def)
(**Nowhere-dense closed sets can be equivalently defined as the fixed points of the frontier operator.*)
lemma nowhereDenseCl_def3: "Cl_2 \<C> \<Longrightarrow> nowhereDenseCl[\<C>] = Fr[\<C>]" using Cl_bnd_nwdn Fr_ClBr boundary_def2 nowhereDenseCl_def by fastforce

end