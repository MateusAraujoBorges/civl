.PHONY:amg2013

CIVL=civl
AMGDIR=../AMG2013

INCLUDES=.:${AMGDIR}:${AMGDIR}/IJ_mv:${AMGDIR}/krylov:${AMGDIR}/parcsr_ls:${AMGDIR}/parcsr_mv:${AMGDIR}/seq_mv:${AMGDIR}/sstruct_mv:${AMGDIR}/struct_mv:${AMGDIR}/test:${AMGDIR}/utilities

SOURCE=${AMGDIR}/IJ_mv/HYPRE_IJMatrix.c ${AMGDIR}/IJ_mv/HYPRE_IJVector.c \
 ${AMGDIR}/IJ_mv/IJMatrix_parcsr.c \
 ${AMGDIR}/IJ_mv/IJVector_parcsr.c \
 ${AMGDIR}/IJ_mv/aux_par_vector.c ${AMGDIR}/IJ_mv/aux_parcsr_matrix.c \
 ${AMGDIR}/krylov/HYPRE_gmres.c ${AMGDIR}/krylov/HYPRE_pcg.c \
 ${AMGDIR}/krylov/gmres.c ${AMGDIR}/krylov/pcg.c \
 ${AMGDIR}/parcsr_ls/HYPRE_parcsr_amg.c ${AMGDIR}/parcsr_ls/HYPRE_parcsr_gmres.c \
 ${AMGDIR}/parcsr_ls/HYPRE_parcsr_pcg.c ${AMGDIR}/parcsr_ls/aux_interp.c \
 ${AMGDIR}/parcsr_ls/gen_redcs_mat.c ${AMGDIR}/parcsr_ls/par_amg.c \
 ${AMGDIR}/parcsr_ls/par_amg_setup.c ${AMGDIR}/parcsr_ls/par_amg_solve.c \
 ${AMGDIR}/parcsr_ls/par_cg_relax_wt.c ${AMGDIR}/parcsr_ls/par_coarse_parms.c \
 ${AMGDIR}/parcsr_ls/par_coarsen.c ${AMGDIR}/parcsr_ls/par_cycle.c \
 ${AMGDIR}/parcsr_ls/par_indepset.c \
 ${AMGDIR}/parcsr_ls/par_interp.c ${AMGDIR}/parcsr_ls/par_jacobi_interp.c \
 ${AMGDIR}/parcsr_ls/par_laplace.c ${AMGDIR}/parcsr_ls/par_laplace_27pt.c \
 ${AMGDIR}/parcsr_ls/par_lr_interp.c ${AMGDIR}/parcsr_ls/par_multi_interp.c \
 ${AMGDIR}/parcsr_ls/par_nodal_systems.c ${AMGDIR}/parcsr_ls/par_rap.c \
 ${AMGDIR}/parcsr_ls/par_rap_communication.c ${AMGDIR}/parcsr_ls/par_relax.c \
 ${AMGDIR}/parcsr_ls/par_relax_interface.c ${AMGDIR}/parcsr_ls/par_relax_more.c \
 ${AMGDIR}/parcsr_ls/par_scaled_matnorm.c ${AMGDIR}/parcsr_ls/par_stats.c \
 ${AMGDIR}/parcsr_ls/par_strength.c ${AMGDIR}/parcsr_ls/par_vardifconv.c \
 ${AMGDIR}/parcsr_ls/partial.c ${AMGDIR}/parcsr_ls/pcg_par.c \
 ${AMGDIR}/parcsr_mv/HYPRE_parcsr_matrix.c \
 ${AMGDIR}/parcsr_mv/HYPRE_parcsr_vector.c ${AMGDIR}/parcsr_mv/new_commpkg.c \
 ${AMGDIR}/parcsr_mv/par_csr_assumed_part.c \
 ${AMGDIR}/parcsr_mv/par_csr_communication.c ${AMGDIR}/parcsr_mv/par_csr_matop.c \
 ${AMGDIR}/parcsr_mv/par_csr_matop_marked.c ${AMGDIR}/parcsr_mv/par_csr_matrix.c \
 ${AMGDIR}/parcsr_mv/par_csr_matvec.c ${AMGDIR}/parcsr_mv/par_vector.c \
 ${AMGDIR}/seq_mv/HYPRE_csr_matrix.c ${AMGDIR}/seq_mv/HYPRE_vector.c \
 ${AMGDIR}/seq_mv/big_csr_matrix.c ${AMGDIR}/seq_mv/csr_matop.c \
 ${AMGDIR}/seq_mv/csr_matrix.c ${AMGDIR}/seq_mv/csr_matvec.c \
 ${AMGDIR}/seq_mv/genpart.c ${AMGDIR}/seq_mv/vector.c \
 ${AMGDIR}/sstruct_mv/HYPRE_sstruct_graph.c \
 ${AMGDIR}/sstruct_mv/HYPRE_sstruct_grid.c \
 ${AMGDIR}/sstruct_mv/HYPRE_sstruct_matrix.c \
 ${AMGDIR}/sstruct_mv/HYPRE_sstruct_stencil.c \
 ${AMGDIR}/sstruct_mv/HYPRE_sstruct_vector.c ${AMGDIR}/sstruct_mv/box_map.c \
 ${AMGDIR}/sstruct_mv/sstruct_axpy.c ${AMGDIR}/sstruct_mv/sstruct_copy.c \
 ${AMGDIR}/sstruct_mv/sstruct_graph.c ${AMGDIR}/sstruct_mv/sstruct_grid.c \
 ${AMGDIR}/sstruct_mv/sstruct_innerprod.c ${AMGDIR}/sstruct_mv/sstruct_matrix.c \
 ${AMGDIR}/sstruct_mv/sstruct_matvec.c \
 ${AMGDIR}/sstruct_mv/sstruct_overlap_innerprod.c \
 ${AMGDIR}/sstruct_mv/sstruct_scale.c ${AMGDIR}/sstruct_mv/sstruct_stencil.c \
 ${AMGDIR}/sstruct_mv/sstruct_vector.c ${AMGDIR}/struct_mv/HYPRE_struct_grid.c \
 ${AMGDIR}/struct_mv/HYPRE_struct_matrix.c \
 ${AMGDIR}/struct_mv/HYPRE_struct_stencil.c \
 ${AMGDIR}/struct_mv/HYPRE_struct_vector.c ${AMGDIR}/struct_mv/assumed_part.c \
 ${AMGDIR}/struct_mv/box.c ${AMGDIR}/struct_mv/box_algebra.c \
 ${AMGDIR}/struct_mv/box_alloc.c ${AMGDIR}/struct_mv/box_boundary.c \
 ${AMGDIR}/struct_mv/box_manager.c ${AMGDIR}/struct_mv/box_neighbors.c \
 ${AMGDIR}/struct_mv/communication_info.c ${AMGDIR}/struct_mv/computation.c \
 ${AMGDIR}/struct_mv/grow.c ${AMGDIR}/struct_mv/new_assemble.c \
 ${AMGDIR}/struct_mv/new_box_neighbors.c ${AMGDIR}/struct_mv/project.c \
 ${AMGDIR}/struct_mv/struct_axpy.c ${AMGDIR}/struct_mv/struct_communication.c \
 ${AMGDIR}/struct_mv/struct_copy.c ${AMGDIR}/struct_mv/struct_grid.c \
 ${AMGDIR}/struct_mv/struct_innerprod.c ${AMGDIR}/struct_mv/struct_io.c \
 ${AMGDIR}/struct_mv/struct_matrix.c ${AMGDIR}/struct_mv/struct_matrix_mask.c \
 ${AMGDIR}/struct_mv/struct_matvec.c \
 ${AMGDIR}/struct_mv/struct_overlap_innerprod.c \
 ${AMGDIR}/struct_mv/struct_scale.c ${AMGDIR}/struct_mv/struct_stencil.c \
 ${AMGDIR}/struct_mv/struct_vector.c ${AMGDIR}/utilities/amg_linklist.c \
 ${AMGDIR}/utilities/binsearch.c ${AMGDIR}/utilities/exchange_data.c \
 ${AMGDIR}/utilities/hypre_error.c ${AMGDIR}/utilities/hypre_memory.c \
 ${AMGDIR}/utilities/hypre_qsort.c ${AMGDIR}/utilities/memory_dmalloc.c \
 ${AMGDIR}/utilities/mpistubs.c ${AMGDIR}/utilities/qsplit.c \
 ${AMGDIR}/utilities/random.c ${AMGDIR}/utilities/thread_mpistubs.c \
 ${AMGDIR}/utilities/threading.c ${AMGDIR}/utilities/timer.c \
 ${AMGDIR}/utilities/timing.c ${AMGDIR}/utilities/umalloc_local.c

all: 
	${CIVL} show -userIncludePath=${INCLUDES} -DHYPRE_SEQUENTIAL -DHYPRE_USING_OPENMP ${SOURCE} main.c 

clean: 
