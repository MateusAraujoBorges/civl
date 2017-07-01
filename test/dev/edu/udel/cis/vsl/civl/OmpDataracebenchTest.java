package edu.udel.cis.vsl.civl;


import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.civl.run.IF.UserInterface;
import org.junit.AfterClass;
import org.junit.Ignore;
import org.junit.Test;

import java.io.File;
import java.io.IOException;
import java.io.PrintStream;

import static org.junit.Assert.assertEquals;

public class OmpDataracebenchTest {

	/* *************************** Static Fields *************************** */

    private static File rootDir = new File(new File("examples/omp/dataracebench-1.0.0"), "micro-benchmarks");

    private static UserInterface ui = new UserInterface();

    private PrintStream out = System.out;

    //private static List<String> codes = Arrays.asList("prune", "sef");

	/* *************************** Helper Methods ************************** */

    private static String filename(String name) {
        return new File(rootDir, name).getPath();
    }

    /**
     * tests an OpenMP program by applying the following transformers in
     * sequence:
     * <ol>
     * <li>OpenMP Pragma transformer;</li>
     * <li>OpenMP to CIVL transformer;</li>
     * <li>Pruner;</li>
     * <li>Side Effect Remover.</li>
     * </ol>
     *
     * @param filenameRoot
     *            The file name of the OpenMP program (without extension).
     * @param raceCondition
     *            The flag to determine whether there is a race condition
     * @throws ABCException
     * @throws IOException
     */
    private void check(String filenameRoot, boolean raceCondition) throws ABCException, IOException {
        assertEquals(!raceCondition, ui.run("verify",
                //"-showProgram",
        		//"-ompNoSimplifier",
                "-input_omp_thread_max=2",
                filename(filenameRoot+".c")));
    }

	/* **************************** Test Methods *************************** */



    @Test(timeout=300000)
    public void antidep1origyes() throws ABCException, IOException{
        check("antidep1-orig-yes",true);
    }

    @Test(timeout=300000)
    public void antidep1varyes() throws ABCException, IOException{
        check("antidep1-var-yes",true);
    }

    @Test(timeout=300000)
    public void antidep2origyes() throws ABCException, IOException{
        check("antidep2-orig-yes",true);
    }

    @Test(timeout=300000)
    public void antidep2varyes() throws ABCException, IOException{
        check("antidep2-var-yes",true);
    }

    @Test(timeout=300000)
    public void doall1origno() throws ABCException, IOException{
        check("doall1-orig-no",false);
    }

    @Test(timeout=300000)
    public void doall2origno() throws ABCException, IOException{
        check("doall2-orig-no",false);
    }

    @Test(timeout=300000)
    public void doallcharorigno() throws ABCException, IOException{
        check("doallchar-orig-no",false);
    }

    @Test(timeout=300000)
    public void firstprivateorigno() throws ABCException, IOException{
        check("firstprivate-orig-no",false);
    }

    @Ignore
    @Test(timeout=300000)
    public void fprintforigno() throws ABCException, IOException{
        check("fprintf-orig-no",false);
    }

    @Test(timeout=300000)
    public void functionparameterorigno() throws ABCException, IOException{
        check("functionparameter-orig-no",false);
    }

    @Test(timeout=300000)
    public void getthreadnumorigno() throws ABCException, IOException{
        check("getthreadnum-orig-no",false);
    }

    @Test(timeout=300000)
    public void indirectaccess1origyes() throws ABCException, IOException{
        check("indirectaccess1-orig-yes",true);
    }

    @Test(timeout=300000)
    public void indirectaccess2origyes() throws ABCException, IOException{
        check("indirectaccess2-orig-yes",true);
    }

    @Test(timeout=300000)
    public void indirectaccess3origyes() throws ABCException, IOException{
        check("indirectaccess3-orig-yes",true);
    }

    @Test(timeout=300000)
    public void indirectaccess4origyes() throws ABCException, IOException{
        check("indirectaccess4-orig-yes",true);
    }

    @Test(timeout=300000)
    public void indirectaccesssharebaseorigno() throws ABCException, IOException{
        check("indirectaccesssharebase-orig-no",false);
    }

    @Test(timeout=300000)
    public void inneronly1origno() throws ABCException, IOException{
        check("inneronly1-orig-no",false);
    }

    @Test(timeout=300000)
    public void inneronly2origno() throws ABCException, IOException{
        check("inneronly2-orig-no",false);
    }

    @Ignore
    @Test(timeout=300000)
    public void jacobiinitializeorigno() throws ABCException, IOException{
        check("jacobiinitialize-orig-no",false);
    }

    @Test(timeout=300000)
    public void jacobikernelorigno() throws ABCException, IOException{
        check("jacobikernel-orig-no",false);
    }

    @Test(timeout=300000)
    public void lastprivateorigno() throws ABCException, IOException{
        check("lastprivate-orig-no",false);
    }

    @Test(timeout=300000)
    public void lastprivatemissingorigyes() throws ABCException, IOException{
        check("lastprivatemissing-orig-yes",true);
    }

    @Test(timeout=300000)
    public void lastprivatemissingvaryes() throws ABCException, IOException{
        check("lastprivatemissing-var-yes",true);
        //nullpointer
    }

    @Test(timeout=300000)
    public void matrixmultiplyorigno() throws ABCException, IOException{
        check("matrixmultiply-orig-no",false);
    }

    @Test(timeout=300000)
    public void matrixvector1origno() throws ABCException, IOException{
        check("matrixvector1-orig-no",false);
    }

    @Test(timeout=300000)
    public void matrixvector2origno() throws ABCException, IOException{
        check("matrixvector2-orig-no",false);
    }

    @Test(timeout=300000)
    public void minusminusorigyes() throws ABCException, IOException{
        check("minusminus-orig-yes",true);
    }

    @Test(timeout=300000)
    public void minusminusvaryes() throws ABCException, IOException{
        check("minusminus-var-yes",true);
    }

    @Test(timeout=300000)
    public void nowaitorigyes() throws ABCException, IOException{
        check("nowait-orig-yes",true);
    }

    @Test(timeout=300000)
    public void outeronly1origno() throws ABCException, IOException{
        check("outeronly1-orig-no",false);
    }

    @Ignore
    @Test(timeout=300000)
    public void outeronly2origno() throws ABCException, IOException{
        check("outeronly2-orig-no",false);
    }

    @Test(timeout=300000)
    public void outofboundsorigyes() throws ABCException, IOException{
        check("outofbounds-orig-yes",true);
    }

    @Test(timeout=300000)
    public void outofboundsvaryes() throws ABCException, IOException{
        check("outofbounds-var-yes",true);
    }

    @Test(timeout=300000)
    public void outputdeporigyes() throws ABCException, IOException{
        check("outputdep-orig-yes",true);
    }

    @Test(timeout=300000)
    public void outputdepvaryes() throws ABCException, IOException{
        check("outputdep-var-yes",true);
    }

    @Ignore
    @Test(timeout=300000)
    public void pireductionorigno() throws ABCException, IOException{
        check("pireduction-orig-no",false);
    }

    @Test(timeout=300000)
    public void plusplusorigyes() throws ABCException, IOException{
        check("plusplus-orig-yes",true);
    }

    @Test(timeout=300000)
    public void pulspulsvaryes() throws ABCException, IOException{
        check("plusplus-var-yes",true);
    }

    @Test(timeout=300000)
    public void pointernoaliasingorigno() throws ABCException, IOException{
        check("pointernoaliasing-orig-no",false);
    }

    @Test(timeout=300000)
    public void privatemissingorigyes() throws ABCException, IOException{
        check("privatemissing-orig-yes",true);
    }

    @Test(timeout=300000)
    public void privatemissingvaryes() throws ABCException, IOException{
        check("privatemissing-var-yes",true);
    }

    @Test(timeout=300000)
    public void reductionmissingorigyes() throws ABCException, IOException{
        check("reductionmissing-orig-yes",true);
    }

    @Test(timeout=300000)
    public void reductionmissingvaryes() throws ABCException, IOException{
        check("reductionmissing-var-yes",true);
    }

    @Test(timeout=300000)
    public void restrictpointer1origno() throws ABCException, IOException{
        check("restrictpointer1-orig-no",false);
    }

    @Test(timeout=300000)
    public void restrictpointer2origno() throws ABCException, IOException{
        check("restrictpointer2-orig-no",false);
    }

    @Test(timeout=300000)
    public void sections1origyes() throws ABCException, IOException{
        check("sections1-orig-yes",true);
    }

    @Test(timeout=300000)
    public void sectionslock1origno() throws ABCException, IOException{
        check("sectionslock1-orig-no",false);
    }

    @Test(timeout=300000)
    public void simd1origno() throws ABCException, IOException{
        check("simd1-orig-no",false);
    }

    @Test(timeout=300000)
    public void simdtruedeporigyes() throws ABCException, IOException{
        check("simdtruedep-orig-yes",true);
    }

    @Test(timeout=300000)
    public void simdtruedepvaryes() throws ABCException, IOException{
        check("simdtruedep-var-yes",true);
    }

    @Test(timeout=300000)
    public void targetparallelfororigno() throws ABCException, IOException{
        check("targetparallelfor-orig-no",false);
    }

    @Test(timeout=300000)
    public void targetparallelfororigyes() throws ABCException, IOException{
        check("targetparallelfor-orig-yes",true);
    }

    @Test(timeout=300000)
    public void taskdep1origno() throws ABCException, IOException{
        check("taskdep1-orig-no",false);
    }

    @Test(timeout=300000)
    public void taskdependmissingorigyes() throws ABCException, IOException{
        check("taskdependmissing-orig-yes",true);
    }

    @Test(timeout=300000)
    public void truedep1origyes() throws ABCException, IOException{
        check("truedep1-orig-yes",true);
    }

    @Test(timeout=300000)
    public void truedep1varyes() throws ABCException, IOException{
        check("truedep1-var-yes",true);
    }

    @Ignore
    @Test(timeout=300000)
    public void truedepfirstdimensionorigyes() throws ABCException, IOException{
        check("truedepfirstdimension-orig-yes",true);
    }

    @Test(timeout=300000)
    public void truedepfirstdimentionvaryes() throws ABCException, IOException{
        check("truedepfirstdimension-var-yes",true);
    }

    @Test(timeout=300000)
    public void truedeplinearorigyes() throws ABCException, IOException{
        check("truedeplinear-orig-yes",true);
    }

    @Test(timeout=300000)
    public void truedeplinearvaryes() throws ABCException, IOException{
        check("truedeplinear-var-yes",true);
    }

    @Test(timeout=300000)
    public void truedepscalarorigyes() throws ABCException, IOException{
        check("truedepscalar-orig-yes",true);
    }

    @Test(timeout=300000)
    public void truedepscalarvaryes() throws ABCException, IOException{
        check("truedepscalar-var-yes",true);
    }

    @Ignore
    @Test(timeout=300000)
    public void truedepseconddimensionorigyes() throws ABCException, IOException{
        check("truedepseconddimension-orig-yes",true);
    }

    @Test(timeout=300000)
    public void truedepseconddimensionvaryes() throws ABCException, IOException{
        check("truedepseconddimension-var-yes",true);
    }


    @Test(timeout=300000)
    public void truedepsingleelementorigyes() throws ABCException, IOException{
        check("truedepsingleelement-orig-yes",true);
    }

    @Test(timeout=300000)
    public void truedepsingleelementvaryes() throws ABCException, IOException{
        check("truedepsingleelement-var-yes",true);
    }

    //The following two tests indicate a bug in ompSimplifier?
    @Test(timeout=300000)
    public void inneronly2origno2() throws ABCException, IOException{
        check("inneronly2-orig-no",false);
    }

    @Test(timeout=300000)
    public void inneronly2origno2pragma() throws ABCException, IOException{
        check("inneronly2-orig-no_2pragmas",false);
    }

    @AfterClass
    public static void tearDownAfterClass() throws Exception {
        ui = null;
        rootDir = null;
    }
}
