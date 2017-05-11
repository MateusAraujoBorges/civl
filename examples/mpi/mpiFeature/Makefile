CC = cc -std=c11
CIVL=civl verify -input_mpi_nprocs=3
COMPARE=civl compare -input_mpi_nprocs=3
DLOPT=-deadlock=potential
MPICC=mpicc -std=c11
MPIEXEC=mpiexec
ISPCC=ispcc -std=c99
ISPEXEC=isp
EXECUTABLES=absolute_dl_bad absolute_dl_good type_match_p2p_bad  \
any_src_bad any_src_good assertion_bad assertion_good collective_match_bad collective_match_good \
comm_dup_bad comm_dup_good dy_buf_bad dy_buf_good input_branch_bad input_branch_good \
matmat_mw_bad matmat_mw_good mpithreads_bad mpithreads_good\
not_single_bad potential_dl_bad rbuf_overflow_bad seq1_bad seq2_bad seq3_bad seq4_bad \
simple_nb_bad tags_bad type_match_p2p_bad \
not_single_good potential_dl_good rbuf_overflow_good seq1_good seq2_good seq3_good seq4_good \
simple_nb_good tags_good type_match_p2p_good

all : absolute_dl any_source assertion collective_match comm_dup\
matmat_mw mpithreads not_single_path potential_dl rbuf_overflow seq1 \
seq2 seq3 seq4 simple_nb tags type_match

isp_all : isp_absolute_dl isp_any_source isp_assertion isp_collective_match isp_comm_dup\
 isp_dy_buf isp_input_branch\
 isp_matmat_mw isp_mpithreads isp_not_single_path isp_potential_dl isp_rbuf_overflow isp_seq1\
 isp_seq2 isp_seq3 isp_seq4 isp_simple_nb isp_tags isp_type_match

run_isp: isprun.sh
	./$<

run_mop: moprun.sh
	./$<

civl_all : civl_absolutedl_bad civl_absolutedl_good civl_any_src_bad civl_any_src_good civl_assertion_bad \
civl_assertion_good \
civl_collective_match_bad civl_collective_match_good civl_comm_dup_bad civl_comm_dup_good  \
civl_dy_buf_bad civl_dy_buf_good \
civl_input_branch_bad civl_input_branch_good civl_matmat_bad civl_matmat_good civl_mpithreads_bad\
civl_mpithreads_good civl_not_single_bad civl_not_single_good civl_potential_bad civl_potential_good\
civl_rbuf_overflow_bad civl_rbuf_overflow_good civl_seq1_bad civl_seq1_good civl_seq2_bad civl_seq2_good \
civl_seq3_bad civl_seq3_good civl_seq4_bad civl_seq4_good  civl_tags_bad civl_tags_good \
civl_type_match_bad civl_type_match_good

################ RUN ################ 
absolute_dl: absolute_dl_bad.c absolute_dl_good.c
	$(MPICC) absolute_dl_bad.c -o absolute_dl_bad
	$(MPICC) absolute_dl_good.c -o absolute_dl_good

run_absolute_dl: absolute_dl
	$(MPIEXEC) -n 3 ./absolute_dl_bad
	$(MPIEXEC) -n 3 ./absolute_dl_good

any_source: any_src_bad.c any_src_good.c
	$(MPICC) -o any_src_bad any_src_bad.c
	$(MPICC) -o any_src_good any_src_good.c

run_any_source: any_source
	$(MPIEXEC) -n 2 ./any_src_bad
	$(MPIEXEC) -n 2 ./any_src_good

assertion: assertion_bad.c assertion_good.c
	$(MPICC) assertion_bad.c -o assertion_bad
	$(MPICC) assertion_good.c -o assertion_good

run_assertion: assertion
	$(MPIEXEC) -n 3 ./assertion_bad
	$(MPIEXEC) -n 3 ./assertion_good

collective_match: collective_match_bad.c collective_match_good.c
	$(MPICC) collective_match_bad.c -o collective_match_bad
	$(MPICC) collective_match_good.c -o collective_match_good

run_collective_match: collective_match
	$(MPIEXEC) -n 3 ./collective_match_bad
	$(MPIEXEC) -n 3 ./collective_match_good

comm_dup: comm_dup_bad.c comm_dup_good.c
	$(MPICC) -o comm_dup_bad comm_dup_bad.c
	$(MPICC) -o comm_dup_good comm_dup_good.c

run_comm_dup: comm_dup
	$(MPIEXEC) -n 3 ./comm_dup_bad
	$(MPIEXEC) -n 3 ./comm_dup_good

dy_buf: dy_buf_bad.c dy_buf_good.c
	$(MPICC) -o dy_buf_bad dy_buf_bad.c
	$(MPICC) -o dy_buf_good dy_buf_good.c

run_dy_buf: dy_buf
	$(MPIEXEC) -n 3 ./dy_buf_bad 
	$(MPIEXEC) -n 3 ./dy_buf_good

input_branch: input_branch_bad.c input_branch_good.c
	$(MPICC) -o input_branch_bad input_branch_bad.c
	$(MPICC) -o input_branch_good input_branch_good.c

run_input_branch: input_branch
	$(MPIEXEC) -n 3 ./input_branch_bad
	$(MPIEXEC) -n 3 ./input_branch_good

matmat_mw: matmat_mw_bad.c matmat_mw_good.c
	$(MPICC) -o matmat_mw_bad matmat_mw_bad.c
	$(MPICC) -o matmat_mw_good matmat_mw_good.c

run_matmat_mw: matmat_mw
	$(MPIEXEC) -n 3 ./matmat_mw_bad
	$(MPIEXEC) -n 3 ./matmat_mw_good

mpithreads: mpithreads_bad.c mpithreads_good.c
	$(MPICC) -o mpithreads_bad mpithreads_bad.c
	$(MPICC) -o mpithreads_good mpithreads_good.c

run_mpithreads: mpithreads
	$(MPIEXEC) -n 2 ./mpithreads_bad
	$(MPIEXEC) -n 2 ./mpithreads_good

not_single_path: not_single_path_bad.c not_single_path_good.c
	$(MPICC) -o not_single_bad not_single_path_bad.c
	$(MPICC) -o not_single_good not_single_path_good.c

run_not_single_path: not_single_path
	$(MPIEXEC) -n 3 ./not_single_bad 
	$(MPIEXEC) -n 3 ./not_single_good

potential_dl: potential_dl_bad.c potential_dl_good.c
	$(MPICC) -o potential_dl_bad potential_dl_bad.c
	$(MPICC) -o potential_dl_good potential_dl_good.c

run_potential_dl: potential_dl
	$(MPIEXEC) -n -3 ./potential_dl_bad
	$(MPIEXEC) -n -3 ./potential_dl_good

rbuf_overflow: rbuf_overflow_bad.c rbuf_overflow_good.c
	$(MPICC) -o rbuf_overflow_bad rbuf_overflow_bad.c
	$(MPICC) -o rbuf_overflow_good rbuf_overflow_good.c

run_rbuf_overflow: rbuf_overflow
	$(MPIEXEC) -n 3 ./rbuf_overflow_bad
	$(MPIEXEC) -n 3 ./rbuf_overflow_good

seq1: seq1_bad.c seq1_good.c
	$(MPICC) -o seq1_bad seq1_bad.c
	$(MPICC) -o seq1_good seq1_good.c

run_seq1: seq1
	$(MPIEXEC) -n 1 ./seq1_bad
	$(MPIEXEC) -n 1 ./seq1_good

seq2: seq2_bad.c seq2_good.c
	$(MPICC) -o seq2_bad seq2_bad.c
	$(MPICC) -o seq2_good seq2_good.c

run_seq2: seq2
	$(MPIEXEC) -n 2 ./seq2_bad
	$(MPIEXEC) -n 2 ./seq2_good

seq3: seq3_bad.c seq3_good.c
	$(MPICC) -o seq3_bad seq3_bad.c
	$(MPICC) -o seq3_good seq3_good.c

run_seq3: seq3
	$(MPIEXEC) -n 3 ./seq3_bad
	$(MPIEXEC) -n 3 ./seq3_good

seq4: seq4_bad.c seq4_good.c
	$(MPICC) -o seq4_bad seq4_bad.c
	$(MPICC) -o seq4_good seq4_good.c

run_seq4: seq4
	$(MPIEXEC) -n 4 ./seq4_bad
	$(MPIEXEC) -n 4 ./seq4_good

simple_nb: simple_nb_bad.c simple_nb_good.c
	$(MPICC) -o simple_nb_bad simple_nb_bad.c
	$(MPICC) -o simple_nb_good simple_nb_good.c

run_simple_nb: simple_nb
	$(MPIEXEC) -n 3 ./simple_nb_bad 
	$(MPIEXEC) -n 3 ./simple_nb_good

tags: tags_bad.c tags_good.c
	$(MPICC) -o tags_bad tags_bad.c
	$(MPICC) -o tags_good tags_good.c

run_tags: tags
	$(MPIEXEC) -n 3 ./tags_bad
	$(MPIEXEC) -n 3 ./tags_good

type_match: type_match_p2p_bad.c type_match_p2p_good.c
	$(MPICC) -o type_match_p2p_bad type_match_p2p_bad.c
	$(MPICC) -o type_match_p2p_good type_match_p2p_good.c

run_type_match: type_match
	$(MPIEXEC) -n 3 ./type_match_p2p_bad 
	$(MPIEXEC) -n 3 ./type_match_p2p_good 
###################  ISP  ######################
isp_absolute_dl: absolute_dl_bad.c absolute_dl_good.c
	$(ISPCC) absolute_dl_bad.c -o absolute_dl_bad
	$(ISPCC) absolute_dl_good.c -o absolute_dl_good

isp_any_source: any_src_bad.c any_src_good.c
	$(ISPCC) -o any_src_bad any_src_bad.c
	$(ISPCC) -o any_src_good any_src_good.c


isp_assertion: assertion_bad.c assertion_good.c
	$(ISPCC) assertion_bad.c -o assertion_bad
	$(ISPCC) assertion_good.c -o assertion_good

isp_collective_match: collective_match_bad.c collective_match_good.c
	$(ISPCC) collective_match_bad.c -o collective_match_bad
	$(ISPCC) collective_match_good.c -o collective_match_good

isp_comm_dup: comm_dup_bad.c comm_dup_good.c
	$(ISPCC) -o comm_dup_bad comm_dup_bad.c
	$(ISPCC) -o comm_dup_good comm_dup_good.c

isp_dy_buf: dy_buf_bad.c dy_buf_good.c
	$(ISPCC) -o dy_buf_bad dy_buf_bad.c
	$(ISPCC) -o dy_buf_good dy_buf_good.c

isp_input_branch: input_branch_bad.c input_branch_good.c
	$(ISPCC) -o input_branch_bad input_branch_bad.c
	$(ISPCC) -o input_branch_good input_branch_good.c

isp_matmat_mw: matmat_mw_bad.c matmat_mw_good.c
	$(ISPCC) -o matmat_mw_bad matmat_mw_bad.c
	$(ISPCC) -o matmat_mw_good matmat_mw_good.c

isp_mpithreads: mpithreads_bad.c mpithreads_good.c
	$(ISPCC) -o mpithreads_bad mpithreads_bad.c
	$(ISPCC) -o mpithreads_good mpithreads_good.c

isp_not_single_path: not_single_path_bad.c not_single_path_good.c
	$(ISPCC) -o not_single_bad not_single_path_bad.c
	$(ISPCC) -o not_single_good not_single_path_good.c

isp_potential_dl: potential_dl_bad.c potential_dl_good.c
	$(ISPCC) -o potential_dl_bad potential_dl_bad.c
	$(ISPCC) -o potential_dl_good potential_dl_good.c

isp_rbuf_overflow: rbuf_overflow_bad.c rbuf_overflow_good.c
	$(ISPCC) -o rbuf_overflow_bad rbuf_overflow_bad.c
	$(ISPCC) -o rbuf_overflow_good rbuf_overflow_good.c

isp_seq1: seq1_bad.c seq1_good.c
	$(ISPCC) -o seq1_bad seq1_bad.c
	$(ISPCC) -o seq1_good seq1_good.c

isp_seq2: seq2_bad.c seq2_good.c
	$(ISPCC) -o seq2_bad seq2_bad.c
	$(ISPCC) -o seq2_good seq2_good.c

isp_seq3: seq3_bad.c seq3_good.c
	$(ISPCC) -o seq3_bad seq3_bad.c
	$(ISPCC) -o seq3_good seq3_good.c

isp_seq4: seq4_bad.c seq4_good.c
	$(ISPCC) -o seq4_bad seq4_bad.c
	$(ISPCC) -o seq4_good seq4_good.c

isp_simple_nb: simple_nb_bad.c simple_nb_good.c
	$(ISPCC) -o simple_nb_bad simple_nb_bad.c
	$(ISPCC) -o simple_nb_good simple_nb_good.c

isp_tags: tags_bad.c tags_good.c
	$(ISPCC) -o tags_bad tags_bad.c
	$(ISPCC) -o tags_good tags_good.c

isp_type_match: type_match_p2p_bad.c type_match_p2p_good.c
	$(ISPCC) -o type_match_p2p_bad type_match_p2p_bad.c
	$(ISPCC) -o type_match_p2p_good type_match_p2p_good.c

###################  CIVL  ###################
civl_absolutedl_bad: absolute_dl_bad.c
	$(CIVL) $<

civl_absolutedl_good: absolute_dl_good.c
	$(CIVL) $<

civl_any_src_bad: any_src_bad.c
	$(CIVL) $<

civl_any_src_good: any_src_good.c
	$(CIVL) $<

civl_assertion_bad: assertion_bad.c
	$(CIVL) $<

civl_assertion_good: assertion_good.c
	$(CIVL) $<

civl_collective_match_bad: collective_match_bad.c
	$(CIVL) $<

civl_collective_match_good: collective_match_good.c
	$(CIVL) $<

civl_comm_dup_bad: comm_dup_bad.c
	$(CIVL) $<

civl_comm_dup_good: comm_dup_good.c
	$(CIVL) $<

civl_dy_buf_bad: dy_buf_bad.c
	$(CIVL) $(DLOPT) $<

civl_dy_buf_good: dy_buf_good.c
	$(CIVL) $(DLOPT) $<

civl_input_branch_bad: input_branch_bad.c
	$(CIVL) $<

civl_input_branch_good: input_branch_good.c
	$(CIVL) $<

civl_matmat_bad: matmat_mw_bad.c
	$(COMPARE) -impl $< -spec matmat_spec.c

civl_matmat_good: matmat_mw_good.c
	$(COMPARE) -impl $< -spec matmat_spec.c

civl_mpithreads_bad: mpithreads_bad.c
	$(CIVL) $<

civl_mpithreads_good: mpithreads_good.c
	$(CIVL) $<

civl_not_single_bad: not_single_path_bad.c
	$(CIVL) $<

civl_not_single_good: not_single_path_good.c
	$(CIVL) $<

civl_potential_bad: potential_dl_bad.c
	$(CIVL) $(DLOPT) $<

civl_potential_good: potential_dl_good.c
	$(CIVL) $(DLOPT) $<

civl_rbuf_overflow_bad: rbuf_overflow_bad.c
	$(CIVL) $<

civl_rbuf_overflow_good: rbuf_overflow_good.c
	$(CIVL) $<

civl_seq1_bad: seq1_bad.c
	$(CIVL) $<

civl_seq1_good: seq1_good.c
	$(CIVL) $<

civl_seq2_bad: seq2_bad.c
	$(CIVL) $<

civl_seq2_good: seq2_good.c
	$(CIVL) $<

civl_seq3_bad: seq3_bad.c
	$(CIVL) $<

civl_seq3_good: seq3_good.c
	$(CIVL) $<

civl_seq4_bad: seq4_bad.c
	$(CIVL) $<

civl_seq4_good: seq4_good.c
	$(CIVL) $<

civl_tags_bad: tags_bad.c
	$(CIVL) $<

civl_tags_good: tags_good.c
	$(CIVL) $<

civl_type_match_bad: type_match_p2p_bad.c
	$(CIVL) $<

civl_type_match_good: type_match_p2p_good.c
	$(CIVL) $<


clean :
	rm -f $(EXECUTABLES) *~ a.out
	rm -rf CIVLREP