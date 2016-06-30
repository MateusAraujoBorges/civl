package edu.udel.cis.vsl.civl.bench;

import java.io.File;
import java.util.Arrays;
import java.util.List;

import edu.udel.cis.vsl.abc.err.IF.ABCException;
import edu.udel.cis.vsl.abc.main.ABCExecutor;
import edu.udel.cis.vsl.abc.main.TranslationTask;

/**
 * java -classpath ${WORKING_DIR}/civl.jar:${WORKING_DIR}/bin
 * edu.udel.cis.vsl.civl.bench.ParserMemoryTest $arg0 $arg1
 * 
 * where $arg0 is the full path to the test file and $arg1 is the number of
 * iteration, ${WORKING_DIR} is your CIVL directory.
 * 
 * @author zmanchun
 *
 */
public class ParserMemoryTest {
	private static Runtime runtime = Runtime.getRuntime();
	private static long mb = 1024 * 1024;
	private static List<String> codes = Arrays.asList("prune", "sef");

	public static void main(String[] args) throws ABCException {
		File testFile = new File(args[0]);
		int n = Integer.parseInt(args[1]);
		TranslationTask task;
		ABCExecutor executor;

		for (int i = 0; i < n; i++) {
			System.out.println("i is " + i);
			task = new TranslationTask(testFile);
			task.addAllTransformCodes(codes);
			executor = new ABCExecutor(task);
			executor.execute();
			System.gc();
			System.out.println("Number of types = "
					+ executor.getFrontEnd().getASTFactory().getTypeFactory()
							.getNumTypes());
			System.out.println("##### Heap utilization statistics [MB] #####");
			System.out.println("Used Memory:"
					+ (runtime.totalMemory() - runtime.freeMemory()) / mb);
			System.out.println("Free Memory:" + runtime.freeMemory() / mb);
			System.out.flush();
		}
	}
}
