package edu.udel.cis.vsl.civl.library.IF;

import java.io.PrintStream;

import edu.udel.cis.vsl.civl.kripke.common.CommonEnabler;
import edu.udel.cis.vsl.civl.model.IF.ModelFactory;
import edu.udel.cis.vsl.civl.semantics.IF.Executor;
import edu.udel.cis.vsl.civl.semantics.IF.SymbolicUtility;

/**
 * The class loader for library enabler/executor.
 * 
 * @author Manchun Zheng (zmanchun)
 * @author Timothy K. Zirkel (zirkel)
 * 
 */
public interface LibraryLoader {

	/**
	 * Get the library executor with the given name.
	 */
	LibraryExecutor getLibraryExecutor(String name, Executor primaryExecutor,
			PrintStream output, PrintStream err, boolean enablePrintf,
			boolean statelessPrintf, ModelFactory modelFacotry,
			SymbolicUtility symbolicUtil);

	/**
	 * Gets the library enabler with the given name.
	 * 
	 * @param name
	 *            The name of the library whose enabler is to be obtained.
	 * @param primaryEnabler
	 *            The CIVL enabler for normal CIVL executions.
	 * @param output
	 *            The print stream to be used in the library enabler.
	 * @param modelFacotry
	 *            The model factory to be used in the library enabler.
	 * @return The library enabler of the given name.
	 */
	LibraryEnabler getLibraryEnabler(String name, CommonEnabler primaryEnabler,
			PrintStream output, ModelFactory modelFacotry,
			SymbolicUtility symbolicUtil);
}
