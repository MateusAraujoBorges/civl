int num_of_inputs_at_223 = 5; int INPUTS_at_223[5]; int input_at_223_counter = 0;int LbranchIdx = 0;int Lbranch[12] = {1,1,1,1,1,1,0,0,0,0,0,0};
extern void __VERIFIER_error () __attribute__ ((__noreturn__));
extern void __VERIFIER_assume (int);
extern int __VERIFIER_nondet_int ();

void error (void) {
    {
__VERIFIER_assume(!((0 == INPUTS_at_223[0]) || (0 == INPUTS_at_223[1]) || (0 == INPUTS_at_223[2]) || (0 == INPUTS_at_223[3]) || (0 == INPUTS_at_223[4])));__VERIFIER_error ();
        return;
    }
}

int q_buf_0;
int q_free;
int q_read_ev;
int q_write_ev;
int p_num_write;
int p_last_write;
int p_dw_st;
int p_dw_pc;
int p_dw_i;
int c_num_read;
int c_last_read;
int c_dr_st;
int c_dr_pc;
int c_dr_i;

int is_do_write_p_triggered (void) {
    int __retres1;
    {
        if ((int) p_dw_pc == 1) {
            if ((int) q_read_ev == 1) {
                __retres1 = 1;
                goto return_label;
            }
            else {
            }
        }
        else {
        }
        __retres1 = 0;
        return_label : return (__retres1);
    }
}

int is_do_read_c_triggered (void) {
    int __retres1;
    {
        if ((int) c_dr_pc == 1) {
            if ((int) q_write_ev == 1) {
                __retres1 = 1;
                goto return_label;
            }
            else {
            }
        }
        else {
        }
        __retres1 = 0;
        return_label : return (__retres1);
    }
}

void immediate_notify_threads (void) {
    int tmp;
    int tmp___0;
    {
        {
            tmp = is_do_write_p_triggered ();
        }
        if (tmp) {
            p_dw_st = 0;
        }
        else {
        }
        {
            tmp___0 = is_do_read_c_triggered ();
        }
        if (tmp___0) {
            c_dr_st = 0;
        }
        else {
        }
        return;
    }
}

void do_write_p (void) {
    {
        if ((int) p_dw_pc == 0) {
            goto DW_ENTRY;
        }
        else {
            if ((int) p_dw_pc == 1) {
                goto DW_WAIT_READ;
            }
            else {
            }
        }
        DW_ENTRY : {
            while (1) {
                while_0_continue :;
                if ((int) q_free == 0) {
                    p_dw_st = 2;
                    p_dw_pc = 1;
                    goto return_label;
                    DW_WAIT_READ :;
                }
                else {
                }
                {
                    q_buf_0 = __VERIFIER_nondet_int ();
                    p_last_write = q_buf_0;
                    p_num_write += 1;
                    q_free = 0;
                    q_write_ev = 1;
                    immediate_notify_threads ();
                    q_write_ev = 2;
                }
            }
            while_0_break :;
        }
        return_label : return;
    }
}

static int a_t;

void do_read_c (void) {
    int a;
    {
        if ((int) c_dr_pc == 0) {
            goto DR_ENTRY;
        }
        else {
            if ((int) c_dr_pc == 1) {
                goto DR_WAIT_WRITE;
            }
            else {
            }
        }
        DR_ENTRY : {
            while (1) {
                while_1_continue :;
                if ((int) q_free == 1) {
                    c_dr_st = 2;
                    c_dr_pc = 1;
                    a_t = a;
                    goto return_label;
                    DR_WAIT_WRITE : a = a_t;
                }
                else {
                }
                {
                    a = q_buf_0;
                    c_last_read = a;
                    c_num_read += 1;
                    q_free = 1;
                    q_read_ev = 1;
                    immediate_notify_threads ();
                    q_read_ev = 2;
                }
                if (p_last_write == c_last_read) {
                    if (p_num_write == c_num_read) {
                    }
                    else {
                        {
                            error ();
                        }
                    }
                }
                else {
                    {
                        error ();
                    }
                }
            }
            while_1_break :;
        }
        return_label : return;
    }
}

void init_threads (void) {
    {
        __VERIFIER_assume (Lbranch [LbranchIdx ++] ? (int) p_dw_i == 1 : ! ((int) p_dw_i == 1)); if ((int) p_dw_i == 1) {
            p_dw_st = 0;
        }
        else {
            p_dw_st = 2;
        }
        __VERIFIER_assume (Lbranch [LbranchIdx ++] ? (int) c_dr_i == 1 : ! ((int) c_dr_i == 1)); if ((int) c_dr_i == 1) {
            c_dr_st = 0;
        }
        else {
            c_dr_st = 2;
        }
        return;
    }
}

int exists_runnable_thread (void) {
    int __retres1;
    {
        __VERIFIER_assume (Lbranch [LbranchIdx ++] ? (int) p_dw_st == 0 : ! ((int) p_dw_st == 0)); if ((int) p_dw_st == 0) {
            __retres1 = 1;
            goto return_label;
        }
        else {
            if ((int) c_dr_st == 0) {
                __retres1 = 1;
                goto return_label;
            }
            else {
            }
        }
        __retres1 = 0;
        return_label : return (__retres1);
    }
}

void eval (void) {
    int tmp;
    int tmp___0;
    int tmp___1;
    {
        {
            while (1) {
                while_2_continue :;
                {
                    tmp___1 = exists_runnable_thread ();
                }
                __VERIFIER_assume (Lbranch [LbranchIdx ++] ? tmp___1 : ! (tmp___1)); if (tmp___1) {
                }
                else {
                    goto while_2_break;
                }
                __VERIFIER_assume (Lbranch [LbranchIdx ++] ? (int) p_dw_st == 0 : ! ((int) p_dw_st == 0)); if ((int) p_dw_st == 0) {
                    {
                        tmp = __VERIFIER_nondet_int ();
                    }
                    __VERIFIER_assume (Lbranch [LbranchIdx ++] ? tmp : ! (tmp)); if (tmp) {
                        {
                            p_dw_st = 1;
                            do_write_p ();
                        }
                    }
                    else {
                        error ();
                    }
                }
                else {
                }
                if ((int) c_dr_st == 0) {
                    {
                        tmp___0 = __VERIFIER_nondet_int ();
                    }
                    if (tmp___0) {
                        {
                            c_dr_st = 1;
                            do_read_c ();
                        }
                    }
                    else {
                    }
                }
                else {
                }
            }
            while_2_break :;
        }
        return;
    }
}

int stop_simulation (void) {
    int tmp;
    int __retres2;
    {
        {
            tmp = exists_runnable_thread ();
        }
        if (tmp) {
            __retres2 = 0;
            goto return_label;
        }
        else {
        }
        __retres2 = 1;
        return_label : return (__retres2);
    }
}

void start_simulation (void) {
    int kernel_st;
    int tmp;
    {
        {
            kernel_st = 0;
            init_threads ();
        }
        {
            int foo = 1;
            while (1) {__VERIFIER_assume (Lbranch [LbranchIdx ++] ? foo : ! (foo)); if (! (foo)) break; {
                while_3_continue :;
                {
                    kernel_st = 1;
                    eval ();
                    tmp = stop_simulation ();
                }
                if (tmp) {
                    goto while_3_break;
                }
                else {
                }
            }}
            while_3_break :;
        }
        return;
    }
}

void init_model (void) {
    {
        q_free = 1;
        q_write_ev = 2;
        q_read_ev = q_write_ev;
        p_num_write = 0;
        p_dw_pc = 0;
        p_dw_i = 1;
        c_num_read = 0;
        c_dr_pc = 0;
        c_dr_i = 1;
        return;
    }
}

int initialize_reads () {
  for (int instrumentation_index=0; instrumentation_index<5; instrumentation_index++) INPUTS_at_223[instrumentation_index] = __VERIFIER_nondet_int();
}

int main (void) {
    initialize_reads ();
    int __retres1;
    {
        {
            init_model ();
            start_simulation ();
        }
        __retres1 = 0;
        return (__retres1);
    }
}

