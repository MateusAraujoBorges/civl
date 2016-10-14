.PHONY:amg2013

CIVL=civl

INCLUDES=-userIncludePath=./AMG2013:AMG2013/IJ_mv:AMG2013/krylov:AMG2013/parcsr_ls:AMG2013/parcsr_mv:AMG2013/seq_mv:AMG2013/sstruct_mv:AMG2013/struct_mv:AMG2013/test:AMG2013/utilities:

ABC_INCLUDES=-iquote ./AMG2013 -iquote AMG2013/IJ_mv -iquote AMG2013/krylov -iquote AMG2013/parcsr_ls -iquote AMG2013/parcsr_mv -iquote AMG2013/seq_mv -iquote AMG2013/sstruct_mv -iquote AMG2013/struct_mv -iquote AMG2013/test -iquote AMG2013/utilities


SOURCE=AMG2013/IJ_mv/HYPRE_IJMatrix.c AMG2013/IJ_mv/HYPRE_IJVector.c \
 AMG2013/IJ_mv/IJMatrix.c AMG2013/IJ_mv/IJMatrix_parcsr.c \
 AMG2013/IJ_mv/IJVector.c AMG2013/IJ_mv/IJVector_parcsr.c \
 AMG2013/IJ_mv/aux_par_vector.c AMG2013/IJ_mv/aux_parcsr_matrix.c \
 AMG2013/krylov/HYPRE_gmres.c AMG2013/krylov/HYPRE_pcg.c \
 AMG2013/krylov/gmres.c AMG2013/krylov/pcg.c \
 AMG2013/parcsr_ls/HYPRE_parcsr_amg.c AMG2013/parcsr_ls/HYPRE_parcsr_gmres.c \
 AMG2013/parcsr_ls/HYPRE_parcsr_pcg.c AMG2013/parcsr_ls/aux_interp.c \
 AMG2013/parcsr_ls/gen_redcs_mat.c AMG2013/parcsr_ls/par_amg.c \
 AMG2013/parcsr_ls/par_amg_setup.c AMG2013/parcsr_ls/par_amg_solve.c \
 AMG2013/parcsr_ls/par_cg_relax_wt.c AMG2013/parcsr_ls/par_coarse_parms.c \
 AMG2013/parcsr_ls/par_coarsen.c AMG2013/parcsr_ls/par_cycle.c \
 AMG2013/parcsr_ls/par_difconv.c AMG2013/parcsr_ls/par_indepset.c \
 AMG2013/parcsr_ls/par_interp.c AMG2013/parcsr_ls/par_jacobi_interp.c \
 AMG2013/parcsr_ls/par_laplace.c AMG2013/parcsr_ls/par_laplace_27pt.c \
 AMG2013/parcsr_ls/par_lr_interp.c AMG2013/parcsr_ls/par_multi_interp.c \
 AMG2013/parcsr_ls/par_nodal_systems.c AMG2013/parcsr_ls/par_rap.c \
 AMG2013/parcsr_ls/par_rap_communication.c AMG2013/parcsr_ls/par_relax.c \
 AMG2013/parcsr_ls/par_relax_interface.c AMG2013/parcsr_ls/par_relax_more.c \
 AMG2013/parcsr_ls/par_scaled_matnorm.c AMG2013/parcsr_ls/par_stats.c \
 AMG2013/parcsr_ls/par_strength.c AMG2013/parcsr_ls/par_vardifconv.c \
 AMG2013/parcsr_ls/partial.c AMG2013/parcsr_ls/pcg_par.c \
 AMG2013/parcsr_mv/HYPRE_parcsr_matrix.c \
 AMG2013/parcsr_mv/HYPRE_parcsr_vector.c AMG2013/parcsr_mv/new_commpkg.c \
 AMG2013/parcsr_mv/par_csr_assumed_part.c \
 AMG2013/parcsr_mv/par_csr_communication.c AMG2013/parcsr_mv/par_csr_matop.c \
 AMG2013/parcsr_mv/par_csr_matop_marked.c AMG2013/parcsr_mv/par_csr_matrix.c \
 AMG2013/parcsr_mv/par_csr_matvec.c AMG2013/parcsr_mv/par_vector.c \
 AMG2013/seq_mv/HYPRE_csr_matrix.c AMG2013/seq_mv/HYPRE_vector.c \
 AMG2013/seq_mv/big_csr_matrix.c AMG2013/seq_mv/csr_matop.c \
 AMG2013/seq_mv/csr_matrix.c AMG2013/seq_mv/csr_matvec.c \
 AMG2013/seq_mv/genpart.c AMG2013/seq_mv/vector.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_graph.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_grid.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_matrix.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_stencil.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_vector.c AMG2013/sstruct_mv/box_map.c \
 AMG2013/sstruct_mv/sstruct_axpy.c AMG2013/sstruct_mv/sstruct_copy.c \
 AMG2013/sstruct_mv/sstruct_graph.c AMG2013/sstruct_mv/sstruct_grid.c \
 AMG2013/sstruct_mv/sstruct_innerprod.c AMG2013/sstruct_mv/sstruct_matrix.c \
 AMG2013/sstruct_mv/sstruct_matvec.c \
 AMG2013/sstruct_mv/sstruct_overlap_innerprod.c \
 AMG2013/sstruct_mv/sstruct_scale.c AMG2013/sstruct_mv/sstruct_stencil.c \
 AMG2013/sstruct_mv/sstruct_vector.c AMG2013/struct_mv/HYPRE_struct_grid.c \
 AMG2013/struct_mv/HYPRE_struct_matrix.c \
 AMG2013/struct_mv/HYPRE_struct_stencil.c \
 AMG2013/struct_mv/HYPRE_struct_vector.c AMG2013/struct_mv/assumed_part.c \
 AMG2013/struct_mv/box.c AMG2013/struct_mv/box_algebra.c \
 AMG2013/struct_mv/box_alloc.c AMG2013/struct_mv/box_boundary.c \
 AMG2013/struct_mv/box_manager.c AMG2013/struct_mv/box_neighbors.c \
 AMG2013/struct_mv/communication_info.c AMG2013/struct_mv/computation.c \
 AMG2013/struct_mv/grow.c AMG2013/struct_mv/new_assemble.c \
 AMG2013/struct_mv/new_box_neighbors.c AMG2013/struct_mv/project.c \
 AMG2013/struct_mv/struct_axpy.c AMG2013/struct_mv/struct_communication.c \
 AMG2013/struct_mv/struct_copy.c AMG2013/struct_mv/struct_grid.c \
 AMG2013/struct_mv/struct_innerprod.c AMG2013/struct_mv/struct_io.c \
 AMG2013/struct_mv/struct_matrix.c AMG2013/struct_mv/struct_matrix_mask.c \
 AMG2013/struct_mv/struct_matvec.c \
 AMG2013/struct_mv/struct_overlap_innerprod.c \
 AMG2013/struct_mv/struct_scale.c AMG2013/struct_mv/struct_stencil.c \
 AMG2013/struct_mv/struct_vector.c AMG2013/utilities/amg_linklist.c \
 AMG2013/utilities/binsearch.c AMG2013/utilities/exchange_data.c \
 AMG2013/utilities/hypre_error.c AMG2013/utilities/hypre_memory.c \
 AMG2013/utilities/hypre_qsort.c AMG2013/utilities/memory_dmalloc.c \
 AMG2013/utilities/mpistubs.c AMG2013/utilities/qsplit.c \
 AMG2013/utilities/random.c AMG2013/utilities/thread_mpistubs.c \
 AMG2013/utilities/threading.c AMG2013/utilities/timer.c \
 AMG2013/utilities/timing.c AMG2013/utilities/umalloc_local.c


SOURCE2=AMG2013/IJ_mv/HYPRE_IJMatrix.c AMG2013/IJ_mv/HYPRE_IJVector.c \
 AMG2013/IJ_mv/IJMatrix_parcsr.c \
 AMG2013/IJ_mv/IJVector_parcsr.c \
 AMG2013/IJ_mv/aux_par_vector.c AMG2013/IJ_mv/aux_parcsr_matrix.c \
 AMG2013/krylov/HYPRE_gmres.c AMG2013/krylov/HYPRE_pcg.c \
 AMG2013/krylov/gmres.c AMG2013/krylov/pcg.c \
 AMG2013/parcsr_ls/HYPRE_parcsr_amg.c AMG2013/parcsr_ls/HYPRE_parcsr_gmres.c \
 AMG2013/parcsr_ls/HYPRE_parcsr_pcg.c AMG2013/parcsr_ls/aux_interp.c \
 AMG2013/parcsr_ls/gen_redcs_mat.c AMG2013/parcsr_ls/par_amg.c \
 AMG2013/parcsr_ls/par_amg_setup.c AMG2013/parcsr_ls/par_amg_solve.c \
 AMG2013/parcsr_ls/par_cg_relax_wt.c AMG2013/parcsr_ls/par_coarse_parms.c \
 AMG2013/parcsr_ls/par_coarsen.c AMG2013/parcsr_ls/par_cycle.c \
 AMG2013/parcsr_ls/par_indepset.c \
 AMG2013/parcsr_ls/par_interp.c AMG2013/parcsr_ls/par_jacobi_interp.c \
 AMG2013/parcsr_ls/par_laplace.c AMG2013/parcsr_ls/par_laplace_27pt.c \
 AMG2013/parcsr_ls/par_lr_interp.c AMG2013/parcsr_ls/par_multi_interp.c \
 AMG2013/parcsr_ls/par_nodal_systems.c AMG2013/parcsr_ls/par_rap.c \
 AMG2013/parcsr_ls/par_rap_communication.c AMG2013/parcsr_ls/par_relax.c \
 AMG2013/parcsr_ls/par_relax_interface.c AMG2013/parcsr_ls/par_relax_more.c \
 AMG2013/parcsr_ls/par_scaled_matnorm.c AMG2013/parcsr_ls/par_stats.c \
 AMG2013/parcsr_ls/par_strength.c AMG2013/parcsr_ls/par_vardifconv.c \
 AMG2013/parcsr_ls/partial.c AMG2013/parcsr_ls/pcg_par.c \
 AMG2013/parcsr_mv/HYPRE_parcsr_matrix.c \
 AMG2013/parcsr_mv/HYPRE_parcsr_vector.c AMG2013/parcsr_mv/new_commpkg.c \
 AMG2013/parcsr_mv/par_csr_assumed_part.c \
 AMG2013/parcsr_mv/par_csr_communication.c AMG2013/parcsr_mv/par_csr_matop.c \
 AMG2013/parcsr_mv/par_csr_matop_marked.c AMG2013/parcsr_mv/par_csr_matrix.c \
 AMG2013/parcsr_mv/par_csr_matvec.c AMG2013/parcsr_mv/par_vector.c \
 AMG2013/seq_mv/HYPRE_csr_matrix.c AMG2013/seq_mv/HYPRE_vector.c \
 AMG2013/seq_mv/big_csr_matrix.c AMG2013/seq_mv/csr_matop.c \
 AMG2013/seq_mv/csr_matrix.c AMG2013/seq_mv/csr_matvec.c \
 AMG2013/seq_mv/genpart.c AMG2013/seq_mv/vector.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_graph.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_grid.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_matrix.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_stencil.c \
 AMG2013/sstruct_mv/HYPRE_sstruct_vector.c AMG2013/sstruct_mv/box_map.c \
 AMG2013/sstruct_mv/sstruct_axpy.c AMG2013/sstruct_mv/sstruct_copy.c \
 AMG2013/sstruct_mv/sstruct_graph.c AMG2013/sstruct_mv/sstruct_grid.c \
 AMG2013/sstruct_mv/sstruct_innerprod.c AMG2013/sstruct_mv/sstruct_matrix.c \
 AMG2013/sstruct_mv/sstruct_matvec.c \
 AMG2013/sstruct_mv/sstruct_overlap_innerprod.c \
 AMG2013/sstruct_mv/sstruct_scale.c AMG2013/sstruct_mv/sstruct_stencil.c \
 AMG2013/sstruct_mv/sstruct_vector.c AMG2013/struct_mv/HYPRE_struct_grid.c \
 AMG2013/struct_mv/HYPRE_struct_matrix.c \
 AMG2013/struct_mv/HYPRE_struct_stencil.c \
 AMG2013/struct_mv/HYPRE_struct_vector.c AMG2013/struct_mv/assumed_part.c \
 AMG2013/struct_mv/box.c AMG2013/struct_mv/box_algebra.c \
 AMG2013/struct_mv/box_alloc.c AMG2013/struct_mv/box_boundary.c \
 AMG2013/struct_mv/box_manager.c AMG2013/struct_mv/box_neighbors.c \
 AMG2013/struct_mv/communication_info.c AMG2013/struct_mv/computation.c \
 AMG2013/struct_mv/grow.c AMG2013/struct_mv/new_assemble.c \
 AMG2013/struct_mv/new_box_neighbors.c AMG2013/struct_mv/project.c \
 AMG2013/struct_mv/struct_axpy.c AMG2013/struct_mv/struct_communication.c \
 AMG2013/struct_mv/struct_copy.c AMG2013/struct_mv/struct_grid.c \
 AMG2013/struct_mv/struct_innerprod.c AMG2013/struct_mv/struct_io.c \
 AMG2013/struct_mv/struct_matrix.c AMG2013/struct_mv/struct_matrix_mask.c \
 AMG2013/struct_mv/struct_matvec.c \
 AMG2013/struct_mv/struct_overlap_innerprod.c \
 AMG2013/struct_mv/struct_scale.c AMG2013/struct_mv/struct_stencil.c \
 AMG2013/struct_mv/struct_vector.c AMG2013/utilities/amg_linklist.c \
 AMG2013/utilities/binsearch.c AMG2013/utilities/exchange_data.c \
 AMG2013/utilities/hypre_error.c AMG2013/utilities/hypre_memory.c \
 AMG2013/utilities/hypre_qsort.c AMG2013/utilities/memory_dmalloc.c \
 AMG2013/utilities/mpistubs.c AMG2013/utilities/qsplit.c \
 AMG2013/utilities/random.c AMG2013/utilities/thread_mpistubs.c \
 AMG2013/utilities/threading.c AMG2013/utilities/timer.c \
 AMG2013/utilities/timing.c AMG2013/utilities/umalloc_local.c

MATTSOURCE=AMG2013/test/matt_test.c \
 AMG2013/parcsr_ls/par_relax_more.c \
 AMG2013/parcsr_mv/par_csr_assumed_part.c \
 AMG2013/parcsr_mv/par_csr_communication.c \
 AMG2013/parcsr_mv/par_csr_matvec.c \
 AMG2013/parcsr_mv/par_vector.c \
 AMG2013/seq_mv/csr_matvec.c \
 AMG2013/seq_mv/genpart.c \
 AMG2013/seq_mv/vector.c \
 AMG2013/utilities/hypre_error.c \
 AMG2013/utilities/hypre_memory.c \
 AMG2013/utilities/random.c


all: 
	${SHOW} ${INCLUDES} AMG2013/test/amg2013.c ${SOURCE}

amg2013: 
	${SHOW} ${INCLUDES} AMG2013/test/amg2013.c 

abc_amg2013: 
	abc -DHYPRE_TIMING $(ABC_INCLUDES)  AMG2013/test/amg2013.c $(SOURCE2) -summarize -prune
	
steve:
	abc -DHYPRE_TIMING $(ABC_INCLUDES)  AMG2013/test/steve_test.c $(SOURCE2) -summarize -prune

matt:
	abc -DHYPRE_TIMING $(ABC_INCLUDES)  AMG2013/test/matt_test.c $(SOURCE2) -summarize -prune

mattcivl:
	${CIVL} show -verbose ${INCLUDES} -DHYPRE_OPENMP $(MATTSOURCE) 

clean: 
